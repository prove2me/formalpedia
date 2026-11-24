-- Prove2me | Theorems.Thm_BSLambda_CertFamily_dist_eq_one_or_dist_eq_one
-- name    : BSLambda.CertFamily.dist_eq_one_or_dist_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:38.467219+00:00
-- url     : https://prove2.me/theorems/893b1f20-7c11-4d55-af76-af42dd02d92e
-- title:
--   Cert Family: dist eq one or dist eq one
-- statement:
--   Orientation of a nonzero off-diagonal entry: one of the two inputs lies at distance
--   exactly one from the other's certificate (Section 11.2).  In either case the conflict
--   coordinate is the only violated literal, by
--   `PartialAssign.violSet_eq_singleton_of_conflict`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L231-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L231-L243

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

theorem BSLambda.CertFamily.dist_eq_one_or_dist_eq_one {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    (F.P (F.owner y)).dist x.1 = 1 ∨ (F.P (F.owner x)).dist y.1 = 1 := by sorry
