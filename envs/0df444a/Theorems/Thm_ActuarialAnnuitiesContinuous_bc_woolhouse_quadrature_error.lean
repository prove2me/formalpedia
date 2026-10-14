-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_woolhouse_quadrature_error
-- name    : ActuarialAnnuitiesContinuous.bc_woolhouse_quadrature_error
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:35:38.107552+00:00
-- url     : https://prove2.me/theorems/0fb52cd6-43a0-41f6-88b7-2536e3bd87a3
-- title:
--   Composite trapezoid correction with rigorous finite-horizon second-derivative error bound
-- statement:
--   Composite trapezoid correction with rigorous finite-horizon second-derivative error bound. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \left|R_m(f)-\int_0^Hf(t)\,dt-\frac{f(0)-f(H)}{2m}\right|\le\frac{HM}{12m^2}
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Composite trapezoid correction with rigorous finite-horizon second-derivative error bound

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcLeftRiemann

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_woolhouse_quadrature_error (H m : ℕ) (f : ℝ → ℝ) (M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) (hd : ∀ t : ℝ, HasDerivAt f (deriv f t) t) (hdd : ∀ t : ℝ, HasDerivAt (deriv f) (deriv (deriv f) t) t) (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (H : ℝ), |deriv (deriv f) t| ≤ M) : |bcLeftRiemann H m f - (∫ t in (0 : ℝ)..(H : ℝ), f t) - (f 0-f H)/(2*(m : ℝ))| ≤ (H : ℝ)*M/(12*(m : ℝ)^2) := by sorry

end ActuarialAnnuitiesContinuous
