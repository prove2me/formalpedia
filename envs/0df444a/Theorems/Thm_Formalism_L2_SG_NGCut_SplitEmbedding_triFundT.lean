-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_triFundT
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.triFundT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:49.21262+00:00
-- url     : https://prove2.me/theorems/84060d98-0a8e-5ea0-9473-cd3e29afc858
-- title:
--   Split Embedding: tri Fund T
-- statement:
--   The Split Embedding construction uses the tri Fund T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/BoxFundT.lean#L91-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/BoxFundT.lean#L91-L200

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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (P : Type) [Fintype P] [DecidableEq P] (α : P → Type) [∀ p, AddCommGroup (α p)]
    [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
    (hBm : ∀ p, Measurable (fun z : (∀ q, α q) × (∀ q, α q) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : ∀ q, α q), B p x 0 = 0)
    (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (A : ∀ p, AddSubgroup (α p)) [∀ p, Countable (A p)]
    (hinv : ∀ γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) → ∃ γ' : ∀ q, α q, (∀ p, γ' p - τ p γ' ∈ A p) ∧
      ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (F : ∀ p, Set (α p)) (hF : ∀ p, MeasurableSet (F p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
    (K : Set (∀ p, α p)) (hK : MeasurableSet K)
    (hKd : ∀ g, ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ mlaw B γ g ∈ K) :
    Measure.pi μ K = ∏ p, μ p (F p) := by sorry
