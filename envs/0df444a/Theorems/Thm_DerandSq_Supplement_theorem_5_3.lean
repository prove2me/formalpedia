-- Prove2me | Theorems.Thm_DerandSq_Supplement_theorem_5_3
-- name    : DerandSq.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:09:34.439996+00:00
-- url     : https://prove2.me/theorems/c18f20de-80a2-40ae-8dbc-4966c7631c85
-- title:
--   Theorem 5.3 — $|\mathbb E\,\mathrm{tr}\,w(B^N) - \tau(w(t))| \le \prod_i d_i^{q_i}\min\{1, 3q^2/N\}$ below the girth
-- statement:
--   Fix $r$ colours, degrees $d_1, \dots, d_r$ and $N \ge 1$. Let $G_{N;i}$ be a $d_i$-regular graph on $[N]$ with adjacency matrix $A_i^N$, let $U_1^N, \dots, U_r^N$ be i.i.d. uniform permutation matrices, and $B_i^N = U_i^N A_i^N U_i^{N*}$ (5.1). Let $w = (i_1, \dots, i_q) \in [r]^q$ with $q \ge 1$, and for $j \in [r]$ let $q_j = |\{a \in [q] : i_a = j\}|$; assume $q_j < \operatorname{girth}(G_{N;j})$ for all $j$. Then
--
--   $$
--   \bigl|\,\mathbb E \operatorname{tr} w(B^N) - \tau(w(t))\,\bigr| \le \prod_{i=1}^r d_i^{q_i}\cdot \min\Bigl\{1, \frac{3q^2}{N}\Bigr\},
--   $$
--
--   where $w(B^N) = B^N_{i_1}\cdots B^N_{i_q}$, $\operatorname{tr}$ is the normalized trace, $w(t) = t_{i_1}\cdots t_{i_q}$ with $t_i = \sum_{j=1}^{d_i}\lambda(m_{i,j})$ on $\ell^2(\Gamma_{\vec d,r})$, and $\tau$ is the canonical trace.
--
--   Normalized by $\prod_i d_i^{q_i}$, the two sides are the probabilities that a $w$-coloured random walk returns to its start in the relabelled coloured graph and in the coloured infinite tree; the theorem says they differ by $O(q^2/N)$ below the girth. It is the expectation step of the weak convergence Theorem 5.2.
--
--   **Formalization Note** $\mathbb E$ is the average over all $\sigma \in S_N^r$; girth is Mathlib's `egirth` ($\top$ for a forest).
--
--   Differences from the source:
--   - reading: q_j < girth(G_{N;i}) (printed index i) → q_j < egirth (G j) for every j; reason: the printed i is an index slip: j is the bound variable of the clause, and the proof (§5.1) needs each colour's count below that colour's girth
--   - encoding: N vertices, bound min{1, 3q²/N} → hypothesis 1 ≤ N; reason: 3q²/N is undefined at N = 0 (Lean would read it as 0)
--   - encoding: E tr w(B^N) with i.i.d. uniform U_i, compared with τ(w(t)) → average over all σ : Fin r → Perm (Fin N) of N⁻¹ · trace, complex modulus of the difference with tauRed; reason: same numbers; τ(w(t)) is a complex number
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 5.3, p.25

import Mathlib
import Definitions.Def_DerandSq_tauRed
import Definitions.Def_DerandSq_Supplement_conjAdj
import Definitions.Def_DerandSq_Supplement_colTree

namespace DerandSq.Supplement

/-- Theorem 5.3 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.25. Let `r` colours, degrees `d_1, …, d_r`, `N ≥ 1`, and
`d_i`-regular graphs `G_{N;i}` on `[N]` with adjacency matrices `A_i`; `B_i = U_i A_i U_i^*` (5.1)
with `U_1, …, U_r` i.i.d. uniform permutation matrices. Let `w = (i_1, …, i_q) ∈ [r]^q`,
`q ≥ 1`, with `q_j = #{a ∈ [q] : i_a = j} < girth(G_{N;j})` for all `j ∈ [r]`. Then
`|E tr w(B^N) − τ(w(t))| ≤ ∏_i d_i^{q_i} · min{1, 3q²/N}`, where `w(B^N) = B_{i_1} ⋯ B_{i_q}`,
`w(t) = t_{i_1} ⋯ t_{i_q}` and `t_i = ∑_j λ(m_{i,j})` on `ℓ²(Γ_{d,r})`.

**Formalization Note** `E` is the average over the uniform `σ : Fin r → Perm (Fin N)`;
`tr X = N⁻¹ · Matrix.trace X` on the real matrices `conjAdj`; `τ` is `DerandSq.tauRed` (a complex
number) and the difference is measured by the complex modulus. The girth condition is imposed on
`G_{N;j}` for every `j` (the printed `G_{N;i}` is an index slip). `egirth = ⊤` for a forest. -/
theorem theorem_5_3 (r : ℕ) (d : Fin r → ℕ) (N : ℕ) (hN : 1 ≤ N)
    (G : Fin r → SimpleGraph (Fin N)) [∀ i, DecidableRel (G i).Adj]
    (hG : ∀ i, (G i).IsRegularOfDegree (d i)) (q : ℕ) (hq : 1 ≤ q) (w : Fin q → Fin r)
    (hgirth : ∀ j, (((Finset.univ.filter fun a => w a = j).card : ℕ) : ℕ∞) < (G j).egirth) :
    ‖((((∑ σ : Fin r → Equiv.Perm (Fin N),
          (N : ℝ)⁻¹ * Matrix.trace (List.ofFn fun a => conjAdj (G (w a)) (σ (w a))).prod) /
          (Fintype.card (Fin r → Equiv.Perm (Fin N)) : ℝ)) : ℝ) : ℂ) -
        DerandSq.tauRed (List.ofFn fun a => colTree d (w a)).prod‖ ≤
      (∏ i, (d i : ℝ) ^ (Finset.univ.filter fun a => w a = i).card) *
        min 1 (3 * (q : ℝ) ^ 2 / N) := by sorry

end DerandSq.Supplement
