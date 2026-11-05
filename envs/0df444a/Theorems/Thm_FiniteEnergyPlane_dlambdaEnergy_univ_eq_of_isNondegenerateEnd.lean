-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.dlambdaEnergy_univ_eq_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:54:20.415198+00:00
-- url     : https://prove2.me/theorems/9ed3417f-be06-4d5f-a9db-b5c0b5576a5c
-- title:
--   The $d\lambda$-energy of a plane with a nondegenerate end equals the period
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level with contact form $\lambda$, and let $\tilde u$ be a finite-energy $\tilde J$-holomorphic plane with a nondegenerate end at $\infty$, in the sense of Hryniewicz's Definition 2.9 with sign $+1$, asymptotic to the periodic Reeb orbit $P = (x, T)$. Then
--   $$\int_{\mathbb{C}} u^* d\lambda = T.$$
--
--   This identifies the total $d\lambda$-energy of every plane in the sets $\Theta(K, P)$ of fast finite-energy planes, and it is used in the compactness analysis of those sets.
--
--   Formalization Note: the integral is `dlambdaEnergy H Set.univ u`, valued in $[0, \infty]$. The dimension is general.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, proof of Corollary 4.9

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The total `dλ`-energy of a finite-energy `J̃`-holomorphic plane with a nondegenerate end at `∞`
(Hryniewicz, Definition 2.9, sign `+1`) asymptotic to the periodic Reeb orbit `P` is the period of
`P`. -/
theorem dlambdaEnergy_univ_eq_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    dlambdaEnergy H Set.univ u = ENNReal.ofReal P.T := by
  sorry

end FiniteEnergyPlane
