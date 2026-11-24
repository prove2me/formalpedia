-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_nonmarker_language
-- name    : BalanceSpecification.MarkerExtension.nonmarker_language
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:09.824293+00:00
-- url     : https://prove2.me/theorems/b5716993-a1a6-4216-9cf7-c6d97f816933
-- title:
--   Marker Extension: nonmarker language
-- statement:
--   No marker-free source word is added by taking the coded closure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L441-L445
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L441-L445

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A] [Fintype A]

theorem BalanceSpecification.MarkerExtension.nonmarker_language {w : Word (Option A)}
    (hw : w ∈ language (shift M hM x s)) (hmarker : none ∉ w) :
    ∃ v ∈ language Y, w = v.map some := by sorry
