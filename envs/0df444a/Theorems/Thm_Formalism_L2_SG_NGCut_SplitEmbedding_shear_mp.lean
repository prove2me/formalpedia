-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_shear_mp
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:08.541403+00:00
-- url     : https://prove2.me/theorems/8c995182-1060-4f14-8ab8-ec51c542af92
-- title:
--   Split Embedding: shear mp
-- statement:
--   The Split Embedding construction uses the shear mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/ShearMp.lean#L52-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/ShearMp.lean#L52-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_ShearMp
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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp : ∀ (n : ℕ) (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ (α : P → Type) [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
      (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
      (h : P → ℕ) (c : ∀ p, (∀ q, α q) → α p), (∀ p, Measurable (c p)) →
      (∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → c p x = c p x') →
      MeasurePreserving (fun g p => g p + c p g) (Measure.pi μ) (Measure.pi μ) := by sorry
