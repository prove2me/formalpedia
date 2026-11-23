-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxOne_term_le
-- name    : Formalism.FourierDecayAlt.P.BoxOne.term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:58.297154+00:00
-- url     : https://prove2.me/theorems/6c07e717-0ad5-435b-8cea-a7f1ea1ac943
-- title:
--   Box One: term le
-- statement:
--   The Box One construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BoxOne.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BoxOne.lean#L36-L47

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BoxOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxOne
open NumberField Finset
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.FourierDecayAlt.P.BoxOne.term_le (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (Kx : ℝ) (hK : 0 ≤ Kx) (l : E)
    (hl0 : l ≠ 0) :
    ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, ((1 / 2 : ℝ) ^ Kx) ^ (Nat.log 2 ⌊w l / x w⌋₊) := by sorry
