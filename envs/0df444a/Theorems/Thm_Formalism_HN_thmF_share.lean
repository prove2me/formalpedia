-- Prove2me | Theorems.Thm_Formalism_HN_thmF_share
-- name    : Formalism.HN.thmF_share
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:09.374459+00:00
-- url     : https://prove2.me/theorems/ab409616-b626-4930-9e4e-f883e9b269c2
-- title:
--   HN: thm F share
-- statement:
--   The HN construction uses the thm F share property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean#L11-L33

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.thmF_share {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤
      (∑ i, (m i : ℝ)) * (u / (u + τ)) := by sorry
