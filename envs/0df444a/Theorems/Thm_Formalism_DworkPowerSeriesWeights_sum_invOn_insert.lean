-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_invOn_insert
-- name    : Formalism.DworkPowerSeriesWeights.sum_invOn_insert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:22.075299+00:00
-- url     : https://prove2.me/theorems/c72a716b-d5d4-4b5e-8149-06b36decdca7
-- title:
--   Dwork Power Series Weights: sum inv On insert
-- statement:
--   The Dwork Power Series Weights construction uses the sum inv On insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L240-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L240-L318

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
variable {R : Type u} [CommRing R]

theorem Formalism.DworkPowerSeriesWeights.sum_invOn_insert (w : Fin n → Fin n → R) (hw : ∀ i j, w i j = w j i)
    (g : Finset (Fin n) → R) (a : Fin n) (s : Finset (Fin n)) (ha : a ∉ s) :
    ∑ σ ∈ invOn (insert a s), edgeW w σ * g ((insert a s).filter (fun i => σ i = i)) =
      ∑ σ ∈ invOn s, edgeW w σ * g (insert a (s.filter (fun i => σ i = i))) +
        ∑ b ∈ s, w a b * ∑ σ ∈ invOn (s.erase b),
          edgeW w σ * g ((s.erase b).filter (fun i => σ i = i)) := by sorry
