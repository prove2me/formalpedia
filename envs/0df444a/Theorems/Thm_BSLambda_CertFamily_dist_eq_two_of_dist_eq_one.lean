-- Prove2me | Theorems.Thm_BSLambda_CertFamily_dist_eq_two_of_dist_eq_one
-- name    : BSLambda.CertFamily.dist_eq_two_of_dist_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:43.028985+00:00
-- url     : https://prove2.me/theorems/3d706f3d-326d-49df-902b-db87eafee31a
-- title:
--   Cert Family: dist eq two of dist eq one
-- statement:
--   The two alternatives of `dist_eq_one_or_dist_eq_one` are exclusive, and in the oriented
--   case the reverse distance is exactly two and is realised by the nearest-point projection: `y`
--   violates both `p` and `q` for `C_i`, and resetting them returns `x` (Section 11.3,
--   column bound).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L274-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L274-L290

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)

theorem BSLambda.CertFamily.dist_eq_two_of_dist_eq_one {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    (F.P (F.owner x)).dist y.1 = 2 ∧ x.1 = (F.P (F.owner x)).proj y.1 := by sorry
