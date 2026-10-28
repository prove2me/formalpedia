-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_rescaled_plane
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_rescaled_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T22:05:27.657591+00:00
-- url     : https://prove2.me/theorems/095eda54-0ff1-4aa5-a7d8-dd39c74a8eaf
-- title:
--   Limits of normalized rescalings of a finite-energy plane on the punctured plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$. Let $u:\mathbb C\to\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic plane such that $|z|\,|\nabla u(z)|$ is bounded on $\mathbb C$, and let $R_k>0$ with $R_k\to\infty$. Put $u_k(z)=e^{-2a(u(R_k))}\,u(R_kz)$. Then there are a subsequence $(u_{k_j})$ and a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb C\setminus\{0\}$ with
--   $$\int_{\mathbb C\setminus\{0\}}w^*d\lambda=0$$
--   such that $u_{k_j}\to w$ in $C^\infty_{\mathrm{loc}}(\mathbb C\setminus\{0\})$.
--
--   **Formalization Note** $|\nabla u|$ is `gradNorm H u`, $a$ is `aCoord H`; "finite-energy curve on $\mathbb C\setminus\{0\}$" is `IsFiniteEnergyCurve H J {z | z ≠ 0} w`; the $d\lambda$-energy is `dlambdaEnergy`; $C^\infty_{\mathrm{loc}}$ convergence is `JHolomorphic.TendstoCInftyLocOn`. The point $R_k$ is the real number $R_k$ viewed in $\mathbb C$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, proof of Theorem 31, p. 537

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of the normalized rescalings of a finite-energy plane (Hofer 1993, p. 537). Let `u` be
a finite-energy `J̃`-holomorphic plane such that `|z| · |∇u(z)|` (the `ℝ`-invariant norm
`gradNorm`) is bounded on `ℂ`, and let `R_k > 0`, `R_k → ∞`. Put
`u_k(z) = e^{-2 a(u(R_k))} u(R_k z)`. Then a subsequence `u_{k_j}` converges in `C^∞_loc(ℂ \ {0})` to
a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ {0}` with `∫_{ℂ \ {0}} w^*dλ = 0`. -/
theorem exists_subseq_tendsto_rescaled_plane {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ) (hR0 : ∀ k, 0 < R k)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((R (φ j) : ℝ) : ℂ))) • u (((R (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} := by
  sorry

end FiniteEnergyPlane
