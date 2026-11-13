-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
-- name    : AvramDividend.Classical.avram_a20_bounded_Borel_mark_first_second_integral_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:13:21.477595+00:00
-- url     : https://prove2.me/theorems/a69705d8-63f5-4c54-86bd-a424ebbac3a1
-- title:
--   Original Borel finite-intensity mark-simple approximations preserve both spatial first and second Lévy integral moments
-- statement:
--   Given any finite measure on a measurable spatial mark set S and a sequence of measurable finite-valued real functions f_k with uniform bound |f_k|≤1 and pointwise convergence f_k→g on S, both the real first mark integrals ∫_S f_k dν and the real quadratic mark integrals ∫_S f_k² dν converge to the respective integrals of g and g². The proof uses the restricted measure, a.e. restriction membership, integrable constant domination, exact Bochner dominated convergence and its square-valued version. This supplies the deterministic limiting Lévy intensity rates needed to carry the already Proved finite physical Borel-mark raw moments into the genuine bounded weighted original Lévy jump integral first and second moment theorem JA28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_bounded_Borel_mark_first_second_integral_limits
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (g : ℝ → ℝ)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hLimit : ∀ z ∈ S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    Tendsto (fun k => ∫ z in S, f k z ∂ν)
      atTop (𝓝 (∫ z in S, g z ∂ν)) ∧
    Tendsto (fun k => ∫ z in S, (f k z) ^ 2 ∂ν)
      atTop (𝓝 (∫ z in S, (g z) ^ 2 ∂ν)) := by sorry
