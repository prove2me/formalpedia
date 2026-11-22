-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_pull
-- name    : Formalism.FourierDecayAlt.P.Jx9.pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:28.886911+00:00
-- url     : https://prove2.me/theorems/ad363ddf-37d7-45ce-adda-a654d392c1fe
-- title:
--   Jx9: pull
-- statement:
--   The Jx9 construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L39-L58

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {α X : Type}

theorem Formalism.FourierDecayAlt.P.Jx9.pull [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ) (h : A5.IsPSD (F.image η) k) :
    A5.IsPSD F (fun x y => k (η x) (η y)) := by sorry
