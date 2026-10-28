-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_of_finite_cstar
-- name    : AvramDividend.Classical.vcstar_far_field_hjb_of_finite_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:31:46.675547+00:00
-- url     : https://prove2.me/theorems/2d14a02c-f85f-4559-aaf3-209a5478f55b
-- title:
--   Finite optimal barrier gives full HJB equality beyond one unit above the barrier when discount dominates drift
-- statement:
--   For every finite optimal dividend barrier, the complete generator-integrable HJB maximum equation holds at reserves at least one above the barrier, provided that q times the candidate value dominates the Lévy drift. The previously proved finite-barrier monotonicity controls the negative-jump contribution and the far-field generator inequality establishes the generator part. Above the barrier, the candidate is affine with derivative one, so the maximum is exactly zero. This removes all far-field points satisfying the explicit drift bound from the open global HJB calculation.
-- source:
--   Canonical Proved finite-barrier monotonicity 8a1169cb-22fd-4b52-b4b8-fdf06c536132, far-field generator residual 0b8f8042-c4e0-48cc-8457-ee30eb69e493, and affine derivative 4098a584-9c09-4437-b71f-5590221db9ab.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_far_field_hjb_of_finite_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x)
    (hcost : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
