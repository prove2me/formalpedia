-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_univ_eq_dlambdaEnergy_of_plane
-- name    : FiniteEnergyPlane.energy_univ_eq_dlambdaEnergy_of_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:54:15.016591+00:00
-- url     : https://prove2.me/theorems/c8f9b706-dda6-4d78-bb76-211b9c5973ea
-- title:
--   The Hofer energy of a nonconstant finite-energy plane equals its $d\lambda$-energy
-- statement:
--   Let $\tilde u = (a, u) : \mathbb{C} \to \mathbb{R} \times S$ be a nonconstant finite-energy $\tilde J$-holomorphic plane in the symplectization of a strictly star-shaped level $S$. Then its Hofer energy equals its $d\lambda$-energy:
--   $$\sup_{\varphi \in \Sigma} \int_{\mathbb{C}} \tilde u^* d(\varphi \lambda) = \int_{\mathbb{C}} u^* d\lambda.$$
--
--   Together with the period identity for planes with nondegenerate ends, this gives the uniform energy bound $E(\tilde u) = T$ on sets of planes asymptotic to one orbit of period $T$, which is the input of bubbling-off and compactness statements.
--
--   Formalization Note: $\Sigma$ is the class `Admissible` of smooth nondecreasing $\varphi : \mathbb{R} \to [0,1]$. Both sides are valued in $[0,\infty]$. The dimension is general.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Section 4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Hofer energy of a nonconstant finite-energy `J̃`-holomorphic plane equals its `dλ`-energy. -/
theorem energy_univ_eq_dlambdaEnergy_of_plane {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    energy H Set.univ u = dlambdaEnergy H Set.univ u := by
  sorry

end FiniteEnergyPlane
