-- Prove2me | Theorems.Thm_DerandSq_Supplement_theorem_5_2
-- name    : DerandSq.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:08:40.048132+00:00
-- url     : https://prove2.me/theorems/e7081817-73df-4c78-950f-2cbcbe94218d
-- title:
--   Theorem 5.2 (corrected: (5.2) for words whose colours have $d_i \ge 1$) — permutation-conjugated high-girth graphs converge weakly to the free trees $t$
-- statement:
--   Fix $r$ colours and degrees $d_1, \dots, d_r$. For each $N$ let $G_{N;1}, \dots, G_{N;r}$ be graphs on $[N]$, $G_{N;i}$ being $d_i$-regular with adjacency matrix $A_i^N$, let $U_1^N, \dots, U_r^N$ be i.i.d. uniform permutation matrices, and set $B_i^N = U_i^N A_i^N U_i^{N*}$ (5.1). Let $t_i = \sum_{j=1}^{d_i}\lambda(m_{i,j})$ on $\ell^2(\Gamma_{\vec d,r})$, $\tau$ the canonical trace and $\operatorname{tr}$ the normalized trace. For a word $w = (i_1, \dots, i_q) \in [r]^q$ write $w(B^N) = B^N_{i_1}\cdots B^N_{i_q}$, $w(t) = t_{i_1}\cdots t_{i_q}$ and $q_j = \#\{a : i_a = j\}$.
--
--   1. **Weak convergence.** If $\operatorname{girth}(G_{N;i}) \to \infty$ as $N \to \infty$ for every $i$, then $B^N$ converges weakly to $t$: for every non-commutative ∗-polynomial $P \in \mathbb C^*\langle x_1, \dots, x_r\rangle$ and every $\varepsilon > 0$,
--   $$
--   \mathbb P\bigl[\,|\operatorname{tr} P(B^N) - \tau(P(t))| \ge \varepsilon\,\bigr] = o_N(1).
--   $$
--   2. **Tail bound (5.2).** For every $N$, every such graphs, every word $w$ whose colours have $d_{i_a} \ge 1$ and with $q_j < \operatorname{girth}(G_{N;j})$ for all $j$, and every $\eta > 0$,
--   $$
--   \mathbb P\Bigl[\,|\operatorname{tr} w(B^N) - \tau(w(t))| \ge \prod_{i=1}^r d_i^{q_i}\Bigl(\frac{3q^2}{N} + \eta\Bigr)\Bigr] \le 2\exp\Bigl(-\frac{\eta^2 N}{32 q^2}\Bigr).
--   $$
--   3. **Choice of $\eta$.** For $q \ge 1$ and $\eta = 8q\sqrt{\log N / N}$ the right side of (5.2) is at most $2/N^2$ for every $N \ge 1$, and the deviation $\prod_i d_i^{q_i}(3q^2/N + \eta)$ tends to $0$ as $N \to \infty$.
--
--   The theorem identifies the joint limit of independently relabelled high-girth graphs as the free product of their limiting trees, and quantifies it.
--
--   **Formalization Note** The family in part 1 is indexed by any sequence of vertex counts $N_n \to \infty$; girth is Mathlib's `egirth` ($\top$ for a forest). Probabilities are over the uniform $\sigma \in S_N^r$. In part 1 the matrices act as operators on $\mathbb C^N$; in part 2 $w(B^N)$ is a product of real matrices. Differences of a real trace and the complex number $\tau(\cdot)$ are measured by the complex modulus.
--
--   Differences from the source:
--   - correction: (5.2) for every word w, with no lower bound on the degrees d_i → (5.2) assumes d_{i_a} ≥ 1 for every letter i_a of w; reason: counterexample: r = 1, d_1 = 0, N = 1, G the empty graph, w = (1), η = 10: tr w(B) = τ(w(t)) = 0 and the threshold is 0, so the event has probability 1 > 2·exp(−100/32) ≈ 0.09; the proof divides by d_i (B̂_i = B_i/d_i)
--   - reading: d_i = O(1) → fixed degrees d : Fin r → ℕ; reason: the limit object Γ_{d,r} and t depend on d, so d cannot vary with N
--   - encoding: a family of graphs G_{N;i} with girth(G_{N;i}) = ω(1), o_N(1) as N → ∞ → an arbitrary sequence of vertex counts N_n → ∞ with graphs G n i, and ∀ M, eventually M < egirth (G n i); reason: d_i-regular graphs need not exist for every N; a family indexed by the N where they exist is such a sequence, and egirth = ⊤ for forests
--   - encoding: weak convergence (2.8): P[|tr P(B^N) − τ(P(t))| ≥ ε] = o_N(1), P ∈ C*⟨x_1,…,x_r⟩ → P : NCPoly 1 (Fin r) evaluated by sEval, tr X = N⁻¹ · trace of the operator on ℂ^N, complex modulus; reason: same polynomials and same numbers (B_i is real symmetric, τ(P(t)) is a complex number)
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 5.2 and (5.2), p.25; (2.8), p.12

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_tauRed
import Definitions.Def_DerandSq_Supplement_conjAdj
import Definitions.Def_DerandSq_Supplement_conjAdjOp
import Definitions.Def_DerandSq_Supplement_colTree
import Definitions.Def_DerandSq_Supplement_sEval

namespace DerandSq.Supplement

/-- Theorem 5.2 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.25, all three parts. Fix `r` colours and degrees `d_1, …, d_r`;
`B_i = U_i A_i U_i^*` (5.1) with `A_i` the adjacency matrix of a `d_i`-regular graph `G_{N;i}`
on `[N]` and `U_1, …, U_r` i.i.d. uniform permutation matrices; `t_i = ∑_j λ(m_{i,j})` on
`ℓ²(Γ_{d,r})`; `tr` is the normalized trace and `τ` the canonical trace.

1. (Weak convergence.) If the graphs come from a family with `girth(G_{N;i}) → ∞` as
   `N → ∞` for every `i`, then `B^N` weakly converges to `t` (2.8): for every scalar
   ∗-polynomial `P` and `ε > 0`, `P[ |tr P(B^N) − τ(P(t))| ≥ ε ] = o_N(1)`.
2. (5.2) For every `N`, every such graphs, every word `w = (i_1, …, i_q) ∈ [r]^q` with
   `q_j = #{a : i_a = j} < girth(G_{N;j})` for all `j`, and every `η > 0`,
   `P[ |tr w(B^N) − τ(w(t))| ≥ ∏_i d_i^{q_i} (3q²/N + η) ] ≤ 2 exp(−η² N / (32 q²))`.
3. For `q ≥ 1` and `η = 8q √(log N / N)` the right side of (5.2) is at most `2/N²` (`N ≥ 1`),
   and the deviation `∏_i d_i^{q_i} (3q²/N + η)` tends to `0` as `N → ∞`.

**Formalization Note** "`d_i = O(1)`" is read as fixed degrees (the limit `t` depends on `d`).
The family in 1. is indexed by an arbitrary sequence of vertex counts `N_n → ∞` (`d_i`-regular
graphs need not exist for every `N`); `girth = ω(1)` is "for every `M`, eventually
`M < egirth`" (`egirth = ⊤` for a forest). Probabilities are `PunctSketch.coinProb` over the
uniform `σ : Fin r → Perm (Fin N)`. In 1. `B_i` acts on `ℂ^N` (`conjAdjOp`), `P(·)` is
`sEval` and `tr X = N⁻¹ · trace X`; in 2. `w(B^N)` is the product of the real matrices
`conjAdj` and `tr` is `N⁻¹ · Matrix.trace`. `τ(·)` is complex and compared through the complex
modulus. Part 2 assumes `d_{i_a} ≥ 1` for each letter of `w` (see the item's differences).
Colours are 0-based. -/
theorem theorem_5_2 (r : ℕ) (d : Fin r → ℕ) :
    (∀ (Nseq : ℕ → ℕ) (G : (n : ℕ) → Fin r → SimpleGraph (Fin (Nseq n)))
        [∀ n i, DecidableRel (G n i).Adj],
        Filter.Tendsto Nseq Filter.atTop Filter.atTop →
        (∀ n i, (G n i).IsRegularOfDegree (d i)) →
        (∀ (i : Fin r) (M : ℕ), ∀ᶠ n in Filter.atTop, (M : ℕ∞) < (G n i).egirth) →
        ∀ (P : DerandSq.NCPoly 1 (Fin r)) (ε : ℝ), 0 < ε →
          Filter.Tendsto
            (fun n : ℕ => PunctSketch.coinProb (fun σ : Fin r → Equiv.Perm (Fin (Nseq n)) =>
              ε ≤ ‖((Nseq n : ℂ))⁻¹ *
                    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (Nseq n)))
                      (sEval P (fun i => conjAdjOp (G n i) (σ i))).toLinearMap -
                  DerandSq.tauRed (sEval P (colTree d))‖))
            Filter.atTop (nhds 0)) ∧
    (∀ (N : ℕ) (G : Fin r → SimpleGraph (Fin N)) [∀ i, DecidableRel (G i).Adj],
        (∀ i, (G i).IsRegularOfDegree (d i)) →
        ∀ (q : ℕ) (w : Fin q → Fin r), (∀ a, 1 ≤ d (w a)) →
        (∀ j, (((Finset.univ.filter fun a => w a = j).card : ℕ) : ℕ∞) < (G j).egirth) →
        ∀ η : ℝ, 0 < η →
          PunctSketch.coinProb (fun σ : Fin r → Equiv.Perm (Fin N) =>
            (∏ i, (d i : ℝ) ^ (Finset.univ.filter fun a => w a = i).card) *
                (3 * (q : ℝ) ^ 2 / N + η) ≤
              ‖(((N : ℝ)⁻¹ *
                    Matrix.trace (List.ofFn fun a => conjAdj (G (w a)) (σ (w a))).prod : ℝ) : ℂ) -
                DerandSq.tauRed (List.ofFn fun a => colTree d (w a)).prod‖) ≤
            2 * Real.exp (-(η ^ 2 * N / (32 * (q : ℝ) ^ 2)))) ∧
    (∀ (q : ℕ) (w : Fin q → Fin r), 1 ≤ q →
        (∀ N : ℕ, 1 ≤ N →
          2 * Real.exp (-((8 * (q : ℝ) * Real.sqrt (Real.log N / N)) ^ 2 * N / (32 * (q : ℝ) ^ 2)))
            ≤ 2 / (N : ℝ) ^ 2) ∧
        Filter.Tendsto
          (fun N : ℕ => (∏ i, (d i : ℝ) ^ (Finset.univ.filter fun a => w a = i).card) *
            (3 * (q : ℝ) ^ 2 / N + 8 * (q : ℝ) * Real.sqrt (Real.log N / N)))
          Filter.atTop (nhds 0)) := by sorry

end DerandSq.Supplement
