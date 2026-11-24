-- Prove2me | Theorems.Thm_BSLambda_CertFamily_ind_flipSet_singleton_eq_true
-- name    : BSLambda.CertFamily.ind_flipSet_singleton_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:02.62002+00:00
-- url     : https://prove2.me/theorems/c50b7753-4999-45ac-a87f-215bee32c42a
-- title:
--   Cert Family: ind flip Set singleton eq true
-- statement:
--   Flipping a coordinate that a certificate leaves free keeps the point inside it, hence
--   positive (Section 11.2).  This is the source of every "one midpoint is positive"
--   argument in `BSLambda/Spectral/GramClass.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L102-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L102-L104

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)

theorem BSLambda.CertFamily.ind_flipSet_singleton_eq_true {i : ι} {x : Input V} (hx : (F.P i).Sat x) {p : V}
    (hp : p ∉ (F.P i).fixedSet) : F.ind (flipSet x {p}) = true := by sorry
