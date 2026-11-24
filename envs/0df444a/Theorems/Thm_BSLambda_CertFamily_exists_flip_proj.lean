-- Prove2me | Theorems.Thm_BSLambda_CertFamily_exists_flip_proj
-- name    : BSLambda.CertFamily.exists_flip_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:35.642602+00:00
-- url     : https://prove2.me/theorems/9701c22c-f01f-4888-9486-6782d9d7f834
-- title:
--   Cert Family: exists flip proj
-- statement:
--   In the oriented case the projection of `x` onto `C_j` is `x^q`, and `y` is obtained
--   from it by flipping the single coordinate `p`, which is fixed by `C_i`
--   (Section 11.3, row bound).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L295-L309
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L295-L309

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

theorem BSLambda.CertFamily.exists_flip_proj {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    ∃ p ∈ (F.P (F.owner x)).fixedSet, y.1 = flipSet ((F.P (F.owner y)).proj x.1) {p} := by sorry
