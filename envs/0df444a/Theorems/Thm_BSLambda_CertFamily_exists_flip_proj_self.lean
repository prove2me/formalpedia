-- Prove2me | Theorems.Thm_BSLambda_CertFamily_exists_flip_proj_self
-- name    : BSLambda.CertFamily.exists_flip_proj_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:46.800504+00:00
-- url     : https://prove2.me/theorems/73658021-7ccc-4138-9928-0e2a7a2c0475
-- title:
--   Cert Family: exists flip proj self
-- statement:
--   The point `x` itself is a single flip of its own projection onto `C_j`, namely at the
--   conflict coordinate, which is fixed by `C_i`.  This removes one option from the row bound
--   of Section 11.3.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L314-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L314-L324

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

theorem BSLambda.CertFamily.exists_flip_proj_self {i j : ι} (hij : i ≠ j) {x : Input V} (hx : (F.P i).Sat x)
    (hd : (F.P j).dist x = 1) :
    ∃ p₀ ∈ (F.P i).fixedSet, x = flipSet ((F.P j).proj x) {p₀} := by sorry
