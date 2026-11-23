-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_factValA
-- name    : Formalism.DworkPowerSeriesWeights.factValA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:04.235694+00:00
-- url     : https://prove2.me/theorems/7f1993d4-d6f5-4fb7-8105-846c6a5ed857
-- title:
--   Dwork Power Series Weights: fact Val A
-- statement:
--   The Dwork Power Series Weights construction uses the fact Val A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LemmaRA.lean#L13-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LemmaRA.lean#L13-L53

import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.factValA {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hlt : ‖(l : K)‖ < 1) {ι : Type v} [Fintype ι] (κ : ι →₀ ℕ) {a : ℕ}
    (ha : 1 ≤ a) (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by sorry
