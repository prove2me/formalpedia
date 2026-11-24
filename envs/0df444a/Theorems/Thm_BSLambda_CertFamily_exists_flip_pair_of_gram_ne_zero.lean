-- Prove2me | Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_gram_ne_zero
-- name    : BSLambda.CertFamily.exists_flip_pair_of_gram_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:24.305373+00:00
-- url     : https://prove2.me/theorems/7e87f738-3483-4082-98ed-a020666dcae1
-- title:
--   Cert Family: exists flip pair of gram ne zero
-- statement:
--   **Classification of a nonzero off-diagonal Gram entry** (Section 11.2).  The two
--   inputs differ in exactly two coordinates `p ≠ q`; the coordinate `q` is the unique
--   conflict of the two owners' certificates, and the other coordinate `p` is fixed by
--   exactly one of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L163-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L163-L176

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

theorem BSLambda.CertFamily.exists_flip_pair_of_gram_ne_zero {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧
      ((p ∈ (F.P (F.owner x)).fixedSet ∧ p ∉ (F.P (F.owner y)).fixedSet) ∨
        (p ∈ (F.P (F.owner y)).fixedSet ∧ p ∉ (F.P (F.owner x)).fixedSet)) := by sorry
