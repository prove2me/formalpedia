-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_uniform_mark_exponential_integral_identity
-- name    : AvramDividend.Classical.chat06_uniform_mark_exponential_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:57:17.495264+00:00
-- url     : https://prove2.me/theorems/0dba1705-8c7f-404f-9ccd-6bde7dd47edf
-- title:
--   Exponential integral identity for Uniform(1,2) claim sizes at every real transform parameter
-- statement:
--   For a unit-density Uniform(1,2) positive claim size, multiplying its negative-exponent Laplace integral by any real theta yields exp(-theta)-exp(-2 theta). The product formulation is valid at theta=0 and avoids division by theta. This supplies the exact jump-mark transform for the uniform downward-jump compound Poisson example.
-- source:
--   Existing source bv_uniform_mark_laplace_unsimplified_identity_chat06_20261020.lean, 31 lines, 1085 bytes, SHA-256 3e16687bb0a6d7a546be57aaf3ff33501276887f54a4729247e8bf565b96984d. Private remote probe 3da02880-e4e0-47b3-bf0d-ee382b6f0099 reached sentinel with zero source errors.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

open Real MeasureTheory

theorem AvramDividend.Classical.chat06_uniform_mark_exponential_integral_identity (θ : ℝ) :
    θ * (∫ x in (1 : ℝ)..2, Real.exp (-θ * x)) =
      Real.exp (-θ) - Real.exp (-(2 * θ)) := by sorry
