-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_comp_exp_mul
-- name    : FiniteEnergyPlane.isNondegenerateEnd_comp_exp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:25:53.128911+00:00
-- url     : https://prove2.me/theorems/817a3849-a117-4c11-8cfe-e6362e16c18f
-- title:
--   Rotating the domain preserves asymptotics at infinity
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be asymptotic to the periodic Reeb orbit $P$ at $\infty$. Then for every $\alpha\in\mathbb{R}$, $z\mapsto u(e^{2\pi i\alpha}z)$ is asymptotic to $P$ at $\infty$.
--
--   Used for reparametrizations of finite-energy planes by rotations.
--
--   **Formalization Note** Asymptotic at $\infty$ is `IsNondegenerateEnd H u cylInf P 1`; it allows an arbitrary phase along the orbit.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u` is asymptotic to `P` at `∞`, then so is `z ↦ u (e^{2πiα} z)` for every real `α`. -/
theorem isNondegenerateEnd_comp_exp_mul {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (α : ℝ) :
    IsNondegenerateEnd H (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z))
      cylInf P 1 := by
  sorry

end FiniteEnergyPlane
