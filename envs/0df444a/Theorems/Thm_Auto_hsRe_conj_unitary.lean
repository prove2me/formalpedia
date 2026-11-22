-- Prove2me | Theorems.Thm_Auto_hsRe_conj_unitary
-- name    : Auto.hsRe_conj_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:52.344515+00:00
-- url     : https://prove2.me/theorems/027a78f5-53dc-45a6-9a62-d3c8bde846cd
-- title:
--   Auto: hs Re conj unitary
-- statement:
--   The Auto construction uses the hs Re conj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L786-L799
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L786-L799

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]

theorem Auto.hsRe_conj_unitary (U : Matrix.unitaryGroup n ℂ) (X Y : Matrix n n ℂ) :
    hsRe (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) (star (U : Matrix n n ℂ) * Y * (U :
      Matrix n n ℂ)) = hsRe X Y := by sorry
