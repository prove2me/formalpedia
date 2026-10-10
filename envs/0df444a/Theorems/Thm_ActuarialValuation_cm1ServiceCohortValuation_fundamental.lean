-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceCohortValuation_fundamental
-- name    : ActuarialValuation.cm1ServiceCohortValuation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:49.122307+00:00
-- url     : https://prove2.me/theorems/3c32d824-d948-46e2-9c58-6606762f8869
-- title:
--   Benefit cashflows and service value: cm1ServiceCohortValuation_fundamental
-- statement:
--   The nontrivial capstone simultaneously proves full multi-year service-table probability conservation, consistent cause-specific pension benefit PV and nonnegative liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(\mathrm{stay})+\sum_{t,j}P(\mathrm{exit}_{t,j})=1,\quad V_{\rm unconditional}=V_{\rm conditional}\ge0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
import Definitions.Def_actuarial_cm1ServiceTotalExits
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Definitions.Def_actuarial_cm1ServiceConditionalPV
import Definitions.Def_actuarial_cm1ServiceTerminalMass

namespace ActuarialValuation

theorem cm1ServiceCohortValuation_fundamental (l : ℕ → ℝ) (d b : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (N m : ℕ) (valid : cm1ServiceValid l d N m) (h0 : 0 < l 0) (hpos : ∀ t ∈ Finset.range N, 0 < l t) (hv : ∀ t ∈ Finset.range N, 0 ≤ v t) (hb : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ b t j) (hd : ∀ t ∈ Finset.range N, ∀ j ∈ Finset.range m, 0 ≤ d t j) : (cm1ServiceTerminalMass l N + cm1ServiceTotalExits d N m / l 0 = 1) ∧ (cm1ServiceBenefitPV v b d l N m = cm1ServiceConditionalPV v b d l N m) ∧ (0 ≤ cm1ServiceBenefitPV v b d l N m) := by sorry

end ActuarialValuation
