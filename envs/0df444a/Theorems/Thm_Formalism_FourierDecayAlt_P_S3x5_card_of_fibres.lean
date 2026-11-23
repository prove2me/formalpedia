-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_of_fibres
-- name    : Formalism.FourierDecayAlt.P.S3x5.card_of_fibres
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:44:12.624934+00:00
-- url     : https://prove2.me/theorems/5e506765-5e88-4351-8e91-446acd9a08aa
-- title:
--   S3x5: card of fibres
-- statement:
--   The S3x5 construction uses the card of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L958-L965
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L958-L965

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x5.card_of_fibres {P A : Type} [Finite P] [Finite A] (f : P → A) (m : ℝ)
    (h : ∀ a, (Nat.card {p // f p = a} : ℝ) = m) : (Nat.card P : ℝ) = Nat.card A * m := by sorry
