-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_shape
-- name    : Formalism.DworkPowerSeriesWeights.low_shape
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:46.552612+00:00
-- url     : https://prove2.me/theorems/b7862364-3101-4097-ba4f-52ac5e294637
-- title:
--   Dwork Power Series Weights: low shape
-- statement:
--   The Dwork Power Series Weights construction uses the low shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L150-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L150-L167

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono

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
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.low_shape {R : Type u} [CommRing R] {N0 N1 Cn : ℕ} (T : Fin N0 → Fin N0 → R)
    (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) T) p hp I).support,
      (∑ y, mono y) = ∑ c, p c ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) ≤ Cn := by sorry
