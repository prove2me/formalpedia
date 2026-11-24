-- Prove2me | Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_dist_eq_one
-- name    : BSLambda.CertFamily.exists_flip_pair_of_dist_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:38.698144+00:00
-- url     : https://prove2.me/theorems/5a487629-a59b-4eb8-bb7a-6059c62281c3
-- title:
--   Cert Family: exists flip pair of dist eq one
-- statement:
--   Oriented form of `exists_flip_pair_of_gram_ne_zero`: once it is known which of the two
--   inputs is the near one, the alternative on `p` is resolved — `C_i` fixes `p` and `C_j` leaves
--   it free, since otherwise `x` would violate both `p` and `q` of `C_j` (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L248-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L248-L268

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

theorem BSLambda.CertFamily.exists_flip_pair_of_dist_eq_one {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧ p ∈ (F.P (F.owner x)).fixedSet ∧
        p ∉ (F.P (F.owner y)).fixedSet := by sorry
