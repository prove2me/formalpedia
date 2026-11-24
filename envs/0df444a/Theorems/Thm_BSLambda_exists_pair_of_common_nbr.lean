-- Prove2me | Theorems.Thm_BSLambda_exists_pair_of_common_nbr
-- name    : BSLambda.exists_pair_of_common_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:59.311426+00:00
-- url     : https://prove2.me/theorems/b9cd8592-d9df-48c2-bfc3-ce31a9399b14
-- title:
--   BSLambda: exists pair of common nbr
-- statement:
--   Two distinct inputs with a common Hamming neighbour differ in exactly two
--   coordinates (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L60-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L60-L69

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.exists_pair_of_common_nbr {x y z : Input V} (hxy : x ≠ y)
    (hxz : hammingDist x z = 1) (hyz : hammingDist y z = 1) :
    ∃ p q : V, p ≠ q ∧ y = flipSet x {p, q} := by sorry
