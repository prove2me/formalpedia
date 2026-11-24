-- Prove2me | Theorems.Thm_BSLambda_CertFamily_ind_flipSet_singleton_eq_true_or
-- name    : BSLambda.CertFamily.ind_flipSet_singleton_eq_true_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:33.55042+00:00
-- url     : https://prove2.me/theorems/a0f3d74a-7a28-46d2-a815-d44c68c93bbc
-- title:
--   Cert Family: ind flip Set singleton eq true or
-- statement:
--   Of the two midpoints between `x` and `y = x^{p,q}`, at least one is positive: some
--   certificate containing `x` or `y` leaves `p` or `q` free, because otherwise `p` and `q`
--   would both be conflict coordinates of the two owners (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L181-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L181-L208

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

theorem BSLambda.CertFamily.ind_flipSet_singleton_eq_true_or {x y : Ones F.ind} {p q : V} (hpq : p ≠ q)
    (hy : y.1 = flipSet x.1 {p, q}) :
    F.ind (flipSet x.1 {p}) = true ∨ F.ind (flipSet x.1 {q}) = true := by sorry
