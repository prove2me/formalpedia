-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_Fw_concat
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.Fw_concat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:35.919647+00:00
-- url     : https://prove2.me/theorems/53a5b854-0497-46fd-8aeb-903ee4a486e3
-- title:
--   Word Monic Extraction: Fw concat
-- statement:
--   The Word Monic Extraction construction uses the Fw concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L248-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L248-L259

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.Fw_concat (Ξ : Sesq M) (X X' : M) (l : Dat R × ℝ) (w : List (Dat R × ℝ)) (P P' : R) :
    Fw Ξ X X' (w ++ [l]) P P' =
      Fw Ξ ((evR l.1.B l.2 + algebraMap ℂ R l.1.s * evR l.1.A l.2) • X) (evR l.1.Av (l.2 + 1) • X')
          w P P' -
        Fw Ξ (evR l.1.A l.2 • X) (evR l.1.Bv (l.2 + 1) • X') w P P' := by sorry
