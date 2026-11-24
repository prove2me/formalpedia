-- Prove2me | Theorems.Thm_BSLambda_eq_flipSet_singleton_of_common_nbr
-- name    : BSLambda.eq_flipSet_singleton_of_common_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:55.419214+00:00
-- url     : https://prove2.me/theorems/6e3b649b-c899-4103-938c-300ce8833a58
-- title:
--   BSLambda: eq flip Set singleton of common nbr
-- statement:
--   The only common Hamming neighbours of `x` and its two-coordinate flip `x^{p,q}` are the
--   two midpoints `x^p` and `x^q`: a third one would sit at distance three from `x^{p,q}`
--   (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L74-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L74-L87

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.eq_flipSet_singleton_of_common_nbr {x z : Input V} {p q : V} (hpq : p ≠ q)
    (hxz : hammingDist x z = 1) (hyz : hammingDist (flipSet x {p, q}) z = 1) :
    z = flipSet x {p} ∨ z = flipSet x {q} := by sorry
