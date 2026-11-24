-- Prove2me | Theorems.Thm_BSLambda_CertFamily_owner_ne_of_gram_ne_zero
-- name    : BSLambda.CertFamily.owner_ne_of_gram_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:29.859952+00:00
-- url     : https://prove2.me/theorems/a8bc2eaa-fe28-4a2f-a1b6-743501992c84
-- title:
--   Cert Family: owner ne of gram ne zero
-- statement:
--   A nonzero off-diagonal Gram entry forces distinct owners (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L112-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L112-L114

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

theorem BSLambda.CertFamily.owner_ne_of_gram_ne_zero {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) : F.owner x ≠ F.owner y := by sorry
