-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_comp_add
-- name    : FiniteEnergyPlane.isNondegenerateEnd_comp_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:15:13.307296+00:00
-- url     : https://prove2.me/theorems/efb97db5-5d2b-48d7-8fa3-4defb9ee89a0
-- title:
--   Translations of the domain preserve a nondegenerate end at infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be strictly star-shaped, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a finite-energy plane whose puncture $\infty$ is nondegenerate with asymptotic limit $P$. Then for every $b\in\mathbb{C}$ the plane $z\mapsto u(z+b)$ also has a nondegenerate puncture at $\infty$ with asymptotic limit $P$.
--
--   It is used for reparametrizations of the leaves of a family of fast planes (Hryniewicz 2012, Lemma 7.3).
--
--   **Formalization Note** The asymptotic condition is `IsNondegenerateEnd H u cylInf P 1`, in the cylindrical coordinates $(s,t)\mapsto e^{2\pi(s+it)}$; the constants in that predicate may change.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If the finite-energy plane `u` is asymptotic to `P` at `∞`, then so is `z ↦ u (z + b)`. -/
theorem isNondegenerateEnd_comp_add {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (b : ℂ) :
    IsNondegenerateEnd H (fun z => u (z + b)) cylInf P 1 := by
  sorry

end FiniteEnergyPlane
