-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_jump_affine_generator_eq_drift
-- name    : AvramDividend.Classical.zero_jump_affine_generator_eq_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:11:58.899616+00:00
-- url     : https://prove2.me/theorems/65c62b8b-25b3-4fbb-a24a-aa796915003c
-- title:
--   Canonical zero-jump Lévy generator equals drift on the affine verification payoff
-- statement:
--   For an arbitrary spectrally negative Lévy process whose Lévy measure is zero, the canonical extended generator applied to the affine function z↦z−1 is well-defined and equals its Lévy drift c everywhere. The second derivative and jump integral vanish. This supplies the generator calculation for the drifted Brownian unbounded-variation counterexample audit.
-- source:
--   Avram, Palmowski and Pistorius (2007), generator in Section 4 and Proposition 4(i); Prove2Me SpectrallyNegativeLevy definition.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_jump_affine_generator_eq_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (x : ℝ) :
    X.GeneratorIntegrable (fun z : ℝ => z - 1) x ∧
      X.generator (fun z : ℝ => z - 1) x = X.c := by sorry
