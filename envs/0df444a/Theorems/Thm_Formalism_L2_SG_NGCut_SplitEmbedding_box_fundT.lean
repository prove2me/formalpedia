-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_box_fundT
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.box_fundT
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:31:46.5328+00:00
-- url     : https://prove2.me/theorems/00fef3a5-a9e2-4a8d-b2b9-464da6ab5dd1
-- title:
--   Split Embedding: box fund T
-- statement:
--   The Split Embedding construction uses the box fund T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/BoxFundT.lean#L20-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/BoxFundT.lean#L20-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFund
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
include hBd hτ hFd

theorem Formalism.L2.SG.NGCut.SplitEmbedding.box_fundT (g : ∀ q, α q) :
    ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ ∀ p, mlaw B γ g p ∈ F p := by sorry
