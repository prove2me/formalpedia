-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDeriv_w_le
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_w_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:39.864066+00:00
-- url     : https://prove2.me/theorems/6b328a37-9811-5959-8afc-e76f2d1b4376
-- title:
--   Fou: norm iterated FDeriv w le
-- statement:
--   The Fou construction uses the norm iterated FDeriv w le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothDecayOfWeighted.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothDecayOfWeighted.lean#L21-L35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.norm_iteratedFDeriv_w_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * au i * au (n - i)) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by sorry
