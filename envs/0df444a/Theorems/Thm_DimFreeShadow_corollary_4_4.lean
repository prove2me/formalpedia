-- Prove2me | Theorems.Thm_DimFreeShadow_corollary_4_4
-- name    : DimFreeShadow.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:59.272823+00:00
-- url     : https://prove2.me/theorems/b6c3ac20-5ae6-4316-8a22-c92487df179c
-- title:
--   Corollary 4.4 — conditional mean bias
-- statement:
--   Let $\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble: $\mathcal X$ finite, $p_x>0$, $\sum_x p_x=1$, each $\rho_x$ a state on $\mathcal H$. Fix $N\ge1$. For effects $E_1,\dots,E_M$, $M\ge1$, with $\theta_j(\rho)=\operatorname{Tr}(E_j\rho)$, Algorithm 2 satisfies
--
--   $$
--   \sum_xp_x\max_{j\in[M]}\Big|\theta_j(\rho_x)-\sum_yK(y\mid x)\theta_j(\rho_y)\Big|\le\sqrt{\frac{\log(2M)}{N}} .
--   $$
--
--   The logarithm is natural. This single measurement controls every observable simultaneously in the mean; Lemma 5.6 turns it into a guarantee for all states.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: max over j ∈ [M] → ⨆ over Fin M, with 1 ≤ M; reason: a real supremum over a nonempty finite type is the maximum
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two Hermitian positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Corollary 4.4, p.19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_outputKernel

namespace DimFreeShadow

/-- **Corollary 4.4 (conditional mean bias)** (arXiv:2608.06345, sha256 a1a42249…,
Corollary 4.4, p.19). For a finite ensemble `{(p_x, ρ_x)}`, a budget `N ≥ 1` and the known
effects `E_1, …, E_M`, Algorithm 2 satisfies
`Σ_x p_x max_{j∈[M]} |θ_j(ρ_x) − Σ_y K(y|x) θ_j(ρ_y)| ≤ √(log(2M)/N)` (23),
with `θ_j(ρ) = Tr(E_j ρ)`.

**Formalization Note** `j` ranges over `Fin M`, `M ≥ 1`, so the `⨆` is a maximum over a
nonempty finite set. Natural logarithm. -/
theorem corollary_4_4 {X d : Type} [Fintype X] [DecidableEq X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (N : ℕ) (hN : 1 ≤ N)
    (M : ℕ) (hM : 1 ≤ M) (E : Fin M → Matrix d d ℂ) (hE : ∀ j, QAlgorithms.IsEffect (E j)) :
    ∑ x, p x * ⨆ j : Fin M,
        |(E j * ρ x).trace.re - ∑ y, outputKernel p ρ N y x * (E j * ρ y).trace.re| ≤
      Real.sqrt (Real.log (2 * M) / N) := by sorry

end DimFreeShadow
