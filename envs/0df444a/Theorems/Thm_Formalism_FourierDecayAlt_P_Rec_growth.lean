-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_growth
-- name    : Formalism.FourierDecayAlt.P.Rec.growth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:05.550036+00:00
-- url     : https://prove2.me/theorems/769f3a70-3658-463c-aa45-893b785a9673
-- title:
--   Rec: growth
-- statement:
--   The Rec construction uses the growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L70-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L70-L115

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real

theorem Formalism.FourierDecayAlt.P.Rec.growth (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ) (ρ : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hε : 0 ≤ ε) (he : ∀ i, 0 ≤ e i) (hσ : ∀ i, 0 ≤ σ i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t))
    (hρ1 : 1 + ε + 2 * a ≤ ρ) :
    ∀ i, i ≤ r + 1 → σ i ≤ Pp e i * ρ ^ i * σ 0 := by sorry
