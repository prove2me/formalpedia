-- Prove2me | Theorems.Thm_Auto_Icc_succ_eq
-- name    : Auto.Icc_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:40.818664+00:00
-- url     : https://prove2.me/theorems/33069774-4ed5-4522-b2db-259ddb57612d
-- title:
--   Auto: Icc succ eq
-- statement:
--   The Auto construction uses the Icc succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L841-L847
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L841-L847

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.Icc_succ_eq (N : ℕ) :
    Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
      insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by sorry
