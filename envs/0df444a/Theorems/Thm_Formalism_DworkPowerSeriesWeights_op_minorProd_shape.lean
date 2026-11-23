-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minorProd_shape
-- name    : Formalism.DworkPowerSeriesWeights.op_minorProd_shape
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:39.250939+00:00
-- url     : https://prove2.me/theorems/0777777b-49a3-4a89-a257-3e73998a67e3
-- title:
--   Dwork Power Series Weights: op minor Prod shape
-- statement:
--   The Dwork Power Series Weights construction uses the op minor Prod shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L213-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L213-L242

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

theorem Formalism.DworkPowerSeriesWeights.op_minorProd_shape {K : Type u} [Field K] {d N0 N1 Cn : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (minorProd (rowOp (N1 := N1) TT T s) p hp I).support) :
    (∀ s' k, s' ≠ s → rowDeg s' k mono = 0) ∧ (∑ k, rowDeg s k mono) = ∑ c, p c ∧
      (∀ k, rowDeg s k mono ≤ Cn) ∧
      (s ∈ TT → (∀ c, 1 ≤ p c) → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 mono = Cn ∧
        ∀ k : Fin N0, k.val ≠ 0 →
          rowDeg s k mono ≤ (Finset.univ.filter (fun c => 2 ≤ p c)).card) := by sorry
