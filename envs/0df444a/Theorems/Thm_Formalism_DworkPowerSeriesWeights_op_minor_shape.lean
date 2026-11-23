-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minor_shape
-- name    : Formalism.DworkPowerSeriesWeights.op_minor_shape
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:17.586168+00:00
-- url     : https://prove2.me/theorems/ca70f351-df11-44a6-a624-6ab2aaeb3cd6
-- title:
--   Dwork Power Series Weights: op minor shape
-- statement:
--   The Dwork Power Series Weights construction uses the op minor shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L165-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L165-L211

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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
open Formalism.IncomingBounds MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.op_minor_shape {K : Type u} [Field K] {d N0 N1 p : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (hp : p ≤ N0) (I : Fin p → Fin N1)
    (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      rowOp (N1 := N1) TT T s ⟨r.val, lt_of_lt_of_le r.isLt hp⟩ (I r')).det.support) :
    (∀ s' k, s' ≠ s → rowDeg s' k mono = 0) ∧ (∑ k, rowDeg s k mono) = p ∧
      (∀ k, rowDeg s k mono ≤ 1) ∧
      (s ∈ TT → 1 ≤ p → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 mono = 1 ∧
        ∀ k : Fin N0, k.val ≠ 0 → rowDeg s k mono ≤ if 2 ≤ p then 1 else 0) := by sorry
