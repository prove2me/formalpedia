-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_thrP_norm
-- name    : Formalism.FourierDecayAlt.P.Jx5.thrP_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:37.960078+00:00
-- url     : https://prove2.me/theorems/a229bdd2-5f4f-47d2-a73b-d3873102f00b
-- title:
--   Jx5: thr P norm
-- statement:
--   The Jx5 construction uses the thr P norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L95-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L95-L111

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)

theorem Formalism.FourierDecayAlt.P.Jx5.thrP_norm (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b : ℕ) (hb : 1 ≤ b)
    (w : InfinitePlace E) :
    thrP G C de de' T T' l b w * (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
      Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') := by sorry
