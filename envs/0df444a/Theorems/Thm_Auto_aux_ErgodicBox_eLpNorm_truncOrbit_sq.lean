-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_truncOrbit_sq
-- name    : Auto.aux_ErgodicBox.eLpNorm_truncOrbit_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:35.92183+00:00
-- url     : https://prove2.me/theorems/8b44b254-1aa7-570a-84a0-bd374e26e646
-- title:
--   aux Ergodic Box: e Lp Norm trunc Orbit sq
-- statement:
--   The aux Ergodic Box construction uses the e Lp Norm trunc Orbit sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2594-L2610
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2594-L2610

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.eLpNorm_truncOrbit_sq
    {X κ : Type*} [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] [MeasurableSingletonClass κ]
    (B : Finset κ) (T : κ → X → X) (f : X → ℝ) (x : X)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hpreal : 0 < p.toReal) :
    eLpNorm (truncOrbit B T f x) p Measure.count ^ 2 =
      orbitPowerSum B T f p.toReal x ^ (2 / p.toReal) := by sorry
