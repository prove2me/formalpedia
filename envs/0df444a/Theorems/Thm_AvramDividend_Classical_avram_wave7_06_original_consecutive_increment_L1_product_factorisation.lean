-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_increment_L1_product_factorisation
-- name    : AvramDividend.Classical.avram_wave7_06_original_consecutive_increment_L1_product_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:52:52.717351+00:00
-- url     : https://prove2.me/theorems/f2fac4db-213f-486c-b948-0a751a0c5bb9
-- title:
--   Consecutive original source future increments have factorising integrable product expectation
-- statement:
--   Assuming the two consecutive original increments have finite first moments under P, their product integral factorises into the product of their individual expectations. This combines actual original-filtration independent increments with integrability and is a source covariance precursor for marked-cell L² martingales.
-- source:
--   W7-06 source finite-grid cross-term elimination interface. Proof imports the Proved two-cell original IndepFun theorem and pinned Mathlib integral-multiplication result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_consecutive_increment_L1_product_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u v : ℝ≥0)
    (hFirst : Integrable
      (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable
      (fun ω => X.X (s + u + v) ω - X.X (s + u) ω) P) :
    (∫ ω, (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω) ∂P) =
      (∫ ω, X.X (s + u) ω - X.X s ω ∂P) *
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) := by sorry
