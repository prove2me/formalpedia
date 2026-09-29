-- Prove2me | Theorems.Thm_FRWCosmology_power_law_solution_exists
-- name    : FRWCosmology.power_law_solution_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:48:08.990813+00:00
-- url     : https://prove2.me/theorems/b103a10e-47da-4520-94c3-f6b30886bbb2
-- title:
--   Existence of the flat power-law FRW solution on $(0,\infty)$
-- statement:
--   For every $G > 0$ and every constant $w \neq -1$ there exists an FRW universe with that
--   value of $G$, with $K = 0$, with time domain $(0,\infty)$, with linear equation of state
--   $p = w\rho$, with positive energy density throughout, and with scale factor
--
--   $$a(t) = t^{\frac{2}{3(1+w)}} .$$
--
--   This is the explicit solution behind eqs. (4.36)–(4.38); its density is
--   $\rho(t) = 3q^2/(8\pi G t^2)$ with $q = 2/3(1+w)$. Its role in the mission is to certify
--   that the hypotheses of the goal theorem are satisfiable, so that the goal is not vacuously
--   true.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, pp. 62-63, eqs. (4.36)-(4.38) (the solution whose existence they describe)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem power_law_solution_exists (G w : ℝ) (hG : 0 < G) (hw : w ≠ -1) :
    ∃ U : FRWUniverse, U.G = G ∧ U.K = 0 ∧ U.I = Set.Ioi 0 ∧ U.LinearEoS w ∧
      (∀ t ∈ U.I, 0 < U.rho t) ∧ (∀ t ∈ U.I, U.a t = t ^ (2 / (3 * (1 + w)))) := by sorry

end FRWCosmology
