-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minor_mem
-- name    : Formalism.DworkPowerSeriesWeights.op_minor_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:48.814302+00:00
-- url     : https://prove2.me/theorems/fd9774ab-9eee-40d0-bfbb-a90ddb1af96f
-- title:
--   Dwork Power Series Weights: op minor mem
-- statement:
--   The Dwork Power Series Weights construction uses the op minor mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L138-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L138-L163

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

theorem Formalism.DworkPowerSeriesWeights.op_minor_mem {K : Type u} [Field K] {d N0 N1 p : ℕ} (s : ZMod d) (A : Fin p → Fin N0 → K)
    (I : Fin p → Fin N1) (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (s, j, I r') : MvPolynomial (ZV d N0 N1) K)).det.support) :
    ∃ τ : Fin p → Fin N0, Function.Injective τ ∧
      (∃ π : Equiv.Perm (Fin p), ∀ i, A (π i) (τ i) ≠ 0) ∧
      mono = ∑ i, Finsupp.single ((s, τ i, I i) : ZV d N0 N1) 1 := by sorry
