-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_firstRow_minor_degree_le_one
-- name    : Formalism.DworkPowerSeriesWeights.firstRow_minor_degree_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:48.663038+00:00
-- url     : https://prove2.me/theorems/66023f5c-29f8-4921-8ad2-d87b3204cc03
-- title:
--   Dwork Power Series Weights: first Row minor degree le one
-- statement:
--   The Dwork Power Series Weights construction uses the first Row minor degree le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L109-L119

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

theorem Formalism.DworkPowerSeriesWeights.firstRow_minor_degree_le_one {R : Type u} [CommRing R] {m N1 p : ℕ} (A : Fin p → Fin m → R)
    (I : Fin p → Fin N1) (mono : Fin m × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (Fin m × Fin N1) R)).det.support) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin m × Fin N1 => y.1.val = 0), mono y) ≤ 1 := by sorry
