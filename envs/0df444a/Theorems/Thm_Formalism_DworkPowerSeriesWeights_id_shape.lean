-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_id_shape
-- name    : Formalism.DworkPowerSeriesWeights.id_shape
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:24.522633+00:00
-- url     : https://prove2.me/theorems/afd090f6-c554-4396-a652-cfecdb982e0e
-- title:
--   Dwork Power Series Weights: id shape
-- statement:
--   The Dwork Power Series Weights construction uses the id shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L169-L181

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

theorem Formalism.DworkPowerSeriesWeights.id_shape {R : Type u} [CommRing R] {N0 N1 Cn : ℕ}
    (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (hp1 : ∀ c, 1 ≤ p c) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) (1 : Matrix (Fin N0) (Fin N0) R)) p hp I).support,
      (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) = Cn := by sorry
