-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_re_real_sum
-- name    : Formalism.FourierDecayAlt.P.PBA.re_real_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:49.025149+00:00
-- url     : https://prove2.me/theorems/bfc11a31-542b-4345-ade7-de5b58530531
-- title:
--   PBA: re real sum
-- statement:
--   The PBA construction uses the re real sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftOfLocal.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftOfLocal.lean#L19-L22

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.PBA.re_real_sum {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by sorry
