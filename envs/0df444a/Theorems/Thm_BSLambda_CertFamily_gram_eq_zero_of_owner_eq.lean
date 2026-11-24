-- Prove2me | Theorems.Thm_BSLambda_CertFamily_gram_eq_zero_of_owner_eq
-- name    : BSLambda.CertFamily.gram_eq_zero_of_owner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:27.181805+00:00
-- url     : https://prove2.me/theorems/7fc418c9-fc2c-45a2-b7f5-59f1008494d4
-- title:
--   Cert Family: gram eq zero of owner eq
-- statement:
--   Two distinct positive inputs with the same owner have no common negative neighbour:
--   both flipped coordinates are free for the common owner, so both midpoints stay inside
--   its certificate and are therefore positive (Section 11.2, case `i = j`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L96-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L96-L109

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

theorem BSLambda.CertFamily.gram_eq_zero_of_owner_eq {x y : Ones F.ind} (hxy : x ≠ y)
    (h : F.owner x = F.owner y) : gram F.ind x y = 0 := by sorry
