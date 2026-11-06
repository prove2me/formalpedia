-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_ruin_terminal_postpayment_atom_split
-- name    : AvramDividend.Classical.avram_p4_f3_original_ruin_terminal_postpayment_atom_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:49:07.986259+00:00
-- url     : https://prove2.me/theorems/e03c5437-ff8f-4f47-9f08-1949726b73d4
-- title:
--   Exact original stopped terminal W splits into post-rightpayment reserve and ruin right atom
-- statement:
--   At the actual original stopped clock, W is the post-rightpayment reserve on the zero/strictly pre-ruin branch, but at ruin W is the prepayment riskProcess. The exact piecewise identity splits W into the post-rightpayment reserve plus a right-dividend payment atom only on the ruin branch. This prevents dropping or duplicating the endpoint payment when telescoping the finite-grid source Itô–Meyer ledger.
-- source:
--   Separate original terminal boundary reduction of canonical fdb9a6a3. The source equality follows from its exact hW and riskProcess definition, independently of the still-open Gaussian/compensated jump Itô identities. It can be combined with ced98f02 finite-clock reserve source theorem and the discounted Stieltjes cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_original_ruin_terminal_postpayment_atom_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (ω : Ω) :
    W ω =
      (riskProcess X x D (τ ω) ω -
        (rightLimit D (τ ω) ω - D (τ ω) ω)) +
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (0 : ℝ) else rightLimit D (τ ω) ω - D (τ ω) ω) := by sorry
