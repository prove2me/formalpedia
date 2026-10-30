-- Prove2me | Theorems.Thm_CompOT_SinkhornConv_theorem_4_2_sinkhorn_global_convergence
-- name    : CompOT.SinkhornConv.theorem_4_2_sinkhorn_global_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:20.328855+00:00
-- url     : https://prove2.me/theorems/e1b57723-0d12-4f06-b2a9-6b98049e5761
-- title:
--   Theorem 4.2: global linear convergence of Sinkhorn's iterations in the Hilbert metric (corrected: second bound of (4.23) uses the half-step coupling)
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be histograms with positive entries, let $C\in\mathbb R^{n\times m}$ be any cost matrix and $\varepsilon>0$; let $K_{i,j} = e^{-C_{i,j}/\varepsilon}$ be the Gibbs kernel and $\lambda = \lambda(K)$ Birkhoff's contraction ratio. Let $(u^{(\ell)}, v^{(\ell)})_{\ell\ge0}$ be Sinkhorn's iterates
--   $$u^{(\ell+1)} = \frac{a}{Kv^{(\ell)}}, \qquad v^{(\ell+1)} = \frac{b}{K^\top u^{(\ell+1)}}, \qquad v^{(0)} = \mathbb 1_m,$$
--   and $P^{(\ell)} = \mathrm{diag}(u^{(\ell)})\,K\,\mathrm{diag}(v^{(\ell)})$. Then there are vectors $u^\star, v^\star$ with positive entries such that:
--   1. $u^{(\ell)}\to u^\star$ and $v^{(\ell)}\to v^\star$;
--   2. $d_{\mathcal H}(u^{(\ell)},u^\star) = O(\lambda^{2\ell})$ and $d_{\mathcal H}(v^{(\ell)},v^\star) = O(\lambda^{2\ell})$ as $\ell\to\infty$ (4.22);
--   3. for every $\ell\ge1$,
--   $$d_{\mathcal H}(u^{(\ell)},u^\star) \le \frac{d_{\mathcal H}(P^{(\ell)}\mathbb 1_m, a)}{1-\lambda^2};$$
--   4. for every $\ell\ge0$,
--   $$d_{\mathcal H}(v^{(\ell)},v^\star) \le \frac{d_{\mathcal H}\big((\mathrm{diag}(u^{(\ell+1)})K\mathrm{diag}(v^{(\ell)}))^\top\mathbb 1_n,\ b\big)}{1-\lambda^2};$$
--   5. $P^\star = \mathrm{diag}(u^\star)\,K\,\mathrm{diag}(v^\star)$ is the unique solution of the entropic optimal transport problem (4.2): a matrix $Q$ is a coupling in $U(a,b)$ minimizing $\langle Q, C\rangle - \varepsilon H(Q)$ over $U(a,b)$ if and only if $Q = P^\star$;
--   6. for every $\ell\ge1$ and all $i,j$,
--   $$\big|\log P^{(\ell)}_{i,j} - \log P^\star_{i,j}\big| \le d_{\mathcal H}(u^{(\ell)},u^\star) + d_{\mathcal H}(v^{(\ell)},v^\star) \tag{4.24}.$$
--
--   Items 3 and 4 are the bounds (4.23): the distance of the scalings to their limits is controlled by the violation of a marginal constraint, which is observable during the run, so they justify the marginal violation as a stopping criterion. Item 6 turns the rate on the scalings into a uniform rate on the log-entries of the coupling.
--
--   **Formalization Note** $O(\cdot)$ is Mathlib's `Asymptotics.IsBigO` along `Filter.atTop`; convergence is entrywise (product topology); $\|\cdot\|_\infty$ in (4.24) is written as a bound for every entry; the entropy in (4.2) uses $0\log 0 = 0$.
--
--   Differences from the source:
--   - correction: d_H(v^(ℓ), v⋆) ≤ d_H(P^(ℓ)ᵀ1_n, b)/(1 − λ(K)²) → d_H(v^(ℓ), v⋆) ≤ d_H((diag(u^(ℓ+1)) K diag(v^(ℓ)))ᵀ1_n, b)/(1 − λ(K)²), for every ℓ ≥ 0; reason: for ℓ ≥ 1, P^(ℓ)ᵀ1_n = v^(ℓ) ⊙ Kᵀu^(ℓ) = b, so the printed bound forces d_H(v^(ℓ), v⋆) = 0, which is false: n = m = 2, a = b = (1/2, 1/2), ε = 1, C = [[−log 2, 0], [0, 0]] (K = [[2, 1], [1, 1]]) gives v^(1) = (6/7, 6/5), v⋆₁/v⋆₂ = √2/2 and d_H(v^(1), v⋆) = log(10/(7√2)) ≈ 0.0101 > 0; the corrected marginal v^(ℓ) ⊙ Kᵀu^(ℓ+1) is what "the second one being similar" (p. 442) proves
--   - reading: ℓ unrestricted in (4.23) and (4.24) → ℓ ≥ 1 in the first bound of (4.23) and in (4.24); reason: u^(0), hence P^(0), is not defined by (4.15); u 0 is left free
--   - reading: a ∈ Σ_n, b ∈ Σ_m (zero entries allowed) → a, b with positive entries; reason: d_H is defined only on positive vectors; with a zero entry in a or b the iterates have zero entries and every d_H in the statement is undefined
--   - encoding: H(P) = −Σ P_{i,j}(log P_{i,j} − 1) with the −∞ convention stated for vectors → 0·log 0 = 0 (Real.log 0 = 0); reason: for positive a, b the minimizer of (4.2) has positive entries and is the same under either convention
--   - generalization: "P⋆ is the unique solution of (4.2)" → the solutions of (4.2) are exactly diag(u⋆) K diag(v⋆), with (u⋆, v⋆) the limits of the iterates; reason: identifies P⋆ with the limiting coupling, as p. 433 states in prose; it specializes to the paper's uniqueness claim
--   - encoding: O(λ(K)^{2ℓ}), ‖·‖_∞, (u^(ℓ), v^(ℓ)) → (u⋆, v⋆), u⋆, v⋆ ∈ ℝ_{+,∗} → Asymptotics.IsBigO Filter.atTop, a bound for every entry (i, j), Filter.Tendsto in the product topology, positivity of u⋆, v⋆ asserted; reason: Lean conventions for the same notions; d_H is defined only on positive vectors
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, Remark 4.14 / Theorem 4.2, eqs. (4.22)–(4.24), p. 441; proof pp. 441–442

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist
import Definitions.Def_CompOT_SinkhornConv_birkhoffLambda
import Definitions.Def_CompOT_SinkhornConv_couplings
import Definitions.Def_CompOT_SinkhornConv_entropicObjective
import Definitions.Def_CompOT_SinkhornConv_gibbsKernel
import Definitions.Def_CompOT_SinkhornConv_IsSinkhornRun

open Matrix

namespace CompOT.SinkhornConv

/-- **Theorem 4.2: global linear convergence of Sinkhorn's iterations in the Hilbert metric.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, Remark 4.14 / Theorem 4.2, p. 441: "One has (u(ℓ), v(ℓ)) → (u⋆, v⋆) and
dH(u(ℓ), u⋆) = O(λ(K)^{2ℓ}), dH(v(ℓ), v⋆) = O(λ(K)^{2ℓ}). (4.22) One also has
dH(u(ℓ), u⋆) ≤ dH(P(ℓ)1m, a)/(1 − λ(K)²), dH(v(ℓ), v⋆) ≤ dH(P(ℓ),⊤1n, b)/(1 − λ(K)²), (4.23)
where we denoted P(ℓ) := diag(u(ℓ))K diag(v(ℓ)). Last, one has
‖log(P(ℓ)) − log(P⋆)‖∞ ≤ dH(u(ℓ), u⋆) + dH(v(ℓ), v⋆), (4.24) where P⋆ is the unique solution
of (4.2)."

Let `a ∈ Σ_n`, `b ∈ Σ_m` have positive entries, `C` be any real `n × m` cost, `ε > 0`,
`K = gibbsKernel C ε` and `λ = λ(K)`, and let `(u^(ℓ), v^(ℓ))` be a run of (4.15) from
`v^(0) = 1_m`, with `P^(ℓ) = diag(u^(ℓ)) K diag(v^(ℓ))`. Then there are positive `u⋆, v⋆` with
1. `u^(ℓ) → u⋆` and `v^(ℓ) → v⋆`;
2. `d_H(u^(ℓ), u⋆) = O(λ^{2ℓ})` and `d_H(v^(ℓ), v⋆) = O(λ^{2ℓ})` as `ℓ → ∞`;
3. for `ℓ ≥ 1`, `d_H(u^(ℓ), u⋆) ≤ d_H(P^(ℓ) 1_m, a) / (1 − λ²)`;
4. for every `ℓ`, `d_H(v^(ℓ), v⋆) ≤ d_H((diag(u^(ℓ+1)) K diag(v^(ℓ)))ᵀ 1_n, b) / (1 − λ²)`
   (corrected second bound of (4.23), see below);
5. `P⋆ = diag(u⋆) K diag(v⋆)` is the unique solution of (4.2): a coupling minimizes the entropic
   objective over `U(a, b)` if and only if it equals `P⋆`;
6. for `ℓ ≥ 1` and all `i, j`, `|log P^(ℓ)_{i,j} − log P⋆_{i,j}| ≤ d_H(u^(ℓ), u⋆) + d_H(v^(ℓ), v⋆)`.

**Formalization Note.**
* Correction. As printed, the second bound of (4.23) uses `P^(ℓ)ᵀ 1_n`, which equals `b` for every
  `ℓ ≥ 1` (it is `v^(ℓ) ⊙ Kᵀ u^(ℓ)`), so it would force `d_H(v^(ℓ), v⋆) = 0`; that is false
  (`n = m = 2`, `a = b = (1/2, 1/2)`, `ε = 1`, `C = [[−log 2, 0], [0, 0]]`:
  `d_H(v^(1), v⋆) = log(10/(7√2)) > 0`). The statement uses the column marginal
  `v^(ℓ) ⊙ Kᵀ u^(ℓ+1)` of the half-step coupling `diag(u^(ℓ+1)) K diag(v^(ℓ))`, which is what the
  paper's "the second one being similar" proves; it holds for every `ℓ ≥ 0`.
* `ℓ ≥ 1` in items 3 and 6: `u^(0)`, hence `P^(0)`, is not defined by (4.15) (`u 0` is free).
* `a, b` positive: `d_H` is defined only on positive vectors, and with a zero entry in `a` or `b`
  the iterates have zero entries and every `d_H` of the theorem is undefined.
* `O(·)` is `Asymptotics.IsBigO Filter.atTop`; convergence is in the product topology of `ℝⁿ`,
  `ℝᵐ`; `‖·‖_∞` is written entrywise; `P^(ℓ) 1_m` is `P ℓ *ᵥ 1`; the entropy uses `0 log 0 = 0`.
* Item 5 identifies the paper's `P⋆` with `diag(u⋆) K diag(v⋆)` (stated in prose on p. 433) and
  asserts it is the unique solution of (4.2). -/
theorem theorem_4_2_sinkhorn_global_convergence {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1)
    (C : Matrix (Fin n) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hrun : IsSinkhornRun (gibbsKernel C ε) a b u v) :
    let K := gibbsKernel C ε
    let lam := birkhoffLambda K
    let P : ℕ → Matrix (Fin n) (Fin m) ℝ := fun ℓ => Matrix.diagonal (u ℓ) * K * Matrix.diagonal (v ℓ)
    ∃ ustar : Fin n → ℝ, ∃ vstar : Fin m → ℝ,
      (∀ i, 0 < ustar i) ∧ (∀ j, 0 < vstar j) ∧
      Filter.Tendsto u Filter.atTop (nhds ustar) ∧ Filter.Tendsto v Filter.atTop (nhds vstar) ∧
      Asymptotics.IsBigO Filter.atTop (fun ℓ => hilbertDist (u ℓ) ustar) (fun ℓ => lam ^ (2 * ℓ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun ℓ => hilbertDist (v ℓ) vstar) (fun ℓ => lam ^ (2 * ℓ)) ∧
      (∀ ℓ, 1 ≤ ℓ → hilbertDist (u ℓ) ustar ≤ hilbertDist (P ℓ *ᵥ 1) a / (1 - lam ^ 2)) ∧
      (∀ ℓ, hilbertDist (v ℓ) vstar ≤
        hilbertDist ((Matrix.diagonal (u (ℓ + 1)) * K * Matrix.diagonal (v ℓ))ᵀ *ᵥ 1) b /
          (1 - lam ^ 2)) ∧
      (∀ Q : Matrix (Fin n) (Fin m) ℝ,
        (Q ∈ couplings a b ∧ IsMinOn (entropicObjective C ε) (couplings a b) Q) ↔
          Q = Matrix.diagonal ustar * K * Matrix.diagonal vstar) ∧
      (∀ ℓ, 1 ≤ ℓ → ∀ i j,
        |Real.log (P ℓ i j) - Real.log ((Matrix.diagonal ustar * K * Matrix.diagonal vstar) i j)| ≤
          hilbertDist (u ℓ) ustar + hilbertDist (v ℓ) vstar) := by sorry

end CompOT.SinkhornConv
