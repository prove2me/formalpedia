-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_le_prod_of_pinned
-- name    : BSLambda.LLL.pr_le_prod_of_pinned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:10.663516+00:00
-- url     : https://prove2.me/theorems/12253a95-bfd0-4078-b6c1-561292a22f96
-- title:
--   LLL: pr le prod of pinned
-- statement:
--   **Pinning with targets read off other coordinates.**  If, on the event `E`, every
--   coordinate of `T` lands in a target set of size at most `m` that depends only on the
--   coordinates of a set `G` disjoint from `T`, then `E` has probability at most
--   `∏ a ∈ T, m / |β a|`.  This is the counting form of "condition on `G`; the coordinates of
--   `T` are still independent and uniform".
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L334-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L334-L353

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ a, DecidableEq (β a)]

theorem BSLambda.LLL.pr_le_prod_of_pinned {G T : Finset A} (hGT : Disjoint G T)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by sorry
