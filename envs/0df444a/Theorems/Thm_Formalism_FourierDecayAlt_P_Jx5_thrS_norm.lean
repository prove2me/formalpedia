-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_thrS_norm
-- name    : Formalism.FourierDecayAlt.P.Jx5.thrS_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:47.582429+00:00
-- url     : https://prove2.me/theorems/e9462aca-6744-40d1-8f07-1d4c66a25146
-- title:
--   Jx5: thr S norm
-- statement:
--   The Jx5 construction uses the thr S norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L77-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L77-L93

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

theorem Formalism.FourierDecayAlt.P.Jx5.thrS_norm (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (w : InfinitePlace E) :
    thrS G C de de' T T' l b s w * (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) := by sorry
