-- Prove2me | Theorems.Thm_BSLambda_CertFamily_card_offMat_row_slice_le
-- name    : BSLambda.CertFamily.card_offMat_row_slice_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:18:56.49686+00:00
-- url     : https://prove2.me/theorems/98916e29-6796-4ea7-ba7e-5726dc0ca02b
-- title:
--   Cert Family: card off Mat row slice le
-- statement:
--   For a fixed second owner `j`, at most `c - 1` inputs `y` give a nonzero oriented
--   entry in the row of `x`: each such `y` is a single flip of `π_{C_j}(x)` at a coordinate
--   fixed by `C_i`, and the flip that returns `x` itself is excluded
--   (Section 11.3, row bound).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L160-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L160-L180

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)

theorem BSLambda.CertFamily.card_offMat_row_slice_le {x : Ones F.ind} {j : ι} (hj : j ≠ F.owner x)
    (hd : (F.P j).dist x.1 = 1) :
    (Finset.univ.filter fun y : Ones F.ind =>
      F.offMat x y ≠ 0 ∧ F.owner y = j).card ≤ F.c - 1 := by sorry
