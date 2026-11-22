-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_dlambdaEnergy_ball_family
-- name    : FiniteEnergyPlane.contDiffOn_dlambdaEnergy_ball_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-22T19:27:10.199689+00:00
-- url     : https://prove2.me/theorems/df38b5c7-1639-4ddb-b619-f36bfd32c6cb
-- title:
--   Regularity of the dλ-energy of a family of planes on discs
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $l\ge0$, $O\subseteq\mathbb{C}$ open, and $f:\mathbb{C}\times\mathbb{C}\to\mathbb{R}^{2n+2}$ of class $C^{l+1}$ on $\mathbb{C}\times O$ such that every slice $f(\cdot,\tau)$, $\tau\in O$, is a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}$. Then the $d\lambda$-energy of the slice $f(\cdot,\tau)$ on the disc $B_\rho(\zeta)$,
--   $$(\zeta,\tau,\rho)\longmapsto\int_{B_\rho(\zeta)}f(\cdot,\tau)^*d\lambda,$$
--   is of class $C^l$ on $\mathbb{C}\times O\times(0,\infty)$.
--
--   It is used to normalize the energy of the members of a family of planes with regular dependence on the parameters.
--
--   **Formalization Note** The $d\lambda$-energy on a set $A$ is `dlambdaEnergy H A u` (an `ℝ≥0∞`-valued integral of the density), taken in `ℝ` with `ENNReal.toReal`; $B_\rho(\zeta)$ is `Metric.ball ζ ρ`. "Finite-energy curve on $\mathbb{C}$" is `IsFiniteEnergyCurve H J Set.univ`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The `dλ`-energy of the slices of a `C^{l+1}` family of finite-energy planes on discs depends
`C^l` on the centre, the parameter and the radius. Let `O ⊆ ℂ` be open and `f : ℂ × ℂ → V n` be
`C^{l+1}` on `ℂ × O`, with every slice `f(·, τ)`, `τ ∈ O`, a finite-energy curve on `ℂ`. Then
`(ζ, τ, ρ) ↦ E_{dλ}(f(·, τ); B_ρ(ζ))` is `C^l` on `ℂ × O × (0, ∞)`. -/
theorem contDiffOn_dlambdaEnergy_ball_family {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (l : ℕ) (O : Set ℂ) (hO : IsOpen O) (f : ℂ × ℂ → V n)
    (hf : ContDiffOn ℝ (l + 1) f (Set.univ ×ˢ O))
    (hslice : ∀ τ ∈ O, IsFiniteEnergyCurve H J Set.univ (fun z => f (z, τ))) :
    ContDiffOn ℝ l (fun p : ℂ × ℂ × ℝ => (dlambdaEnergy H (ball p.1 p.2.2) (fun z => f (z, p.2.1))).toReal)
      (Set.univ ×ˢ O ×ˢ Set.Ioi 0) := by
  sorry

end FiniteEnergyPlane
