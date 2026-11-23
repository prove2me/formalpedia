-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_prod_shape
-- name    : Formalism.DworkPowerSeriesWeights.op_prod_shape
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:42.450157+00:00
-- url     : https://prove2.me/theorems/042c81d3-0e2c-41c5-8443-c3a2f14e4bdf
-- title:
--   Dwork Power Series Weights: op prod shape
-- statement:
--   The Dwork Power Series Weights construction uses the op prod shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L244-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean#L244-L297

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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

theorem Formalism.DworkPowerSeriesWeights.op_prod_shape {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
    (κ : ZV d N0 N1 →₀ ℕ)
    (hκ : κ ∈ (∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s)).support)
    (s : ZMod d) :
    (∑ k, rowDeg s k κ) = ∑ c, p s c ∧ (∀ k, rowDeg s k κ ≤ colN s) ∧
      (s ∈ TT → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 κ = colN s ∧
        ∀ k : Fin N0, k.val ≠ 0 →
          rowDeg s k κ ≤ (Finset.univ.filter (fun c => 2 ≤ p s c)).card) := by sorry
