-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_comp_smul
-- name    : FiniteEnergyPlane.isNondegenerateEnd_comp_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T21:18:43.053811+00:00
-- url     : https://prove2.me/theorems/e0c2a932-50ba-4982-9523-741f2134175c
-- title:
--   Positive dilations of the domain preserve a nondegenerate end at infinity
-- statement:
--   Let $H:\mathbb{R}^{2n+2}\to\mathbb{R}$, $P$ a periodic Reeb orbit on $S=H^{-1}(1)$, and $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ a map whose puncture $\infty$ is nondegenerate with asymptotic limit $P$. Then for every $\rho>0$ the map $z\mapsto u(\rho z)$ also has a nondegenerate puncture at $\infty$ with asymptotic limit $P$.
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

/-- If `u` is asymptotic to `P` at `∞`, then so is `z ↦ u (ρ z)` for every `ρ > 0`. -/
theorem isNondegenerateEnd_comp_smul {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (ρ : ℝ) (hρ : 0 < ρ) :
    IsNondegenerateEnd H (fun z => u (ρ • z)) cylInf P 1 := by
  sorry

end FiniteEnergyPlane
