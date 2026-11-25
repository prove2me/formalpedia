-- Prove2me | Theorems.Thm_Formalism_IndefR_Leaf_Proofs_exists_haar_measure_with_density
-- name    : Formalism.IndefR.Leaf.Proofs.exists_haar_measure_with_density
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:24.681449+00:00
-- url     : https://prove2.me/theorems/16a0bf86-686d-4527-8799-b4ae309ec105
-- title:
--   Proofs: exists haar measure with density
-- statement:
--   The Proofs construction uses the exists haar measure with density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/MinfUniqueP.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/MinfUniqueP.lean#L8-L16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUnique
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_MinfUniqueP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Leaf Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory Formalism.BasicNotions

theorem Formalism.IndefR.Leaf.Proofs.exists_haar_measure_with_density (p q : ℕ) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ∃ m : Measure (UpqT p q), m.IsHaarMeasure ∧ OmegaDensity m c := by sorry
