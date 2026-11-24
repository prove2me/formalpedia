-- Prove2me | Theorems.Thm_BSLambda_CertFamily_mem_fixedSet_of_ind_flipSet_singleton_eq_false
-- name    : BSLambda.CertFamily.mem_fixedSet_of_ind_flipSet_singleton_eq_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:38.81554+00:00
-- url     : https://prove2.me/theorems/cc6d00d1-6c7c-48a1-a08a-1115ee3b8bfa
-- title:
--   Cert Family: mem fixed Set of ind flip Set singleton eq false
-- statement:
--   Contrapositive of `ind_flipSet_singleton_eq_true`: a negative single flip of a positive
--   input can only happen at a coordinate that the input's own certificate fixes
--   (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L109-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L109-L114

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

theorem BSLambda.CertFamily.mem_fixedSet_of_ind_flipSet_singleton_eq_false {i : ι} {x : Input V}
    (hx : (F.P i).Sat x) {p : V} (hp : F.ind (flipSet x {p}) = false) :
    p ∈ (F.P i).fixedSet := by sorry
