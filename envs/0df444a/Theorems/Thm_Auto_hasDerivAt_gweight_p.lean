-- Prove2me | Theorems.Thm_Auto_hasDerivAt_gweight_p
-- name    : Auto.hasDerivAt_gweight_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:56.16436+00:00
-- url     : https://prove2.me/theorems/5813ff99-8bf1-4a83-a787-f0e69f296cf0
-- title:
--   Auto: has Deriv At gweight p
-- statement:
--   The Auto construction uses the has Deriv At gweight p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2993-L2997
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2993-L2997

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]

theorem Auto.hasDerivAt_gweight_p (u : ι → ℝ) (h σ p : ℝ) (i : ι) :
    HasDerivAt (fun q => gweight u h σ q i) (-(h * gaussianD 1 σ (u i - p))) p := by sorry
