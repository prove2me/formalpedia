-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_der_fn
-- name    : Formalism.FourierDecayAlt.P.Mx2.der_fn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:31.145356+00:00
-- url     : https://prove2.me/theorems/e0a622c1-da8d-4060-b18b-fa383edc0ba6
-- title:
--   Mx2: der fn
-- statement:
--   The Mx2 construction uses the der fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L92-L103

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx2.der_fn (a b : Fn r) (v w : Var r) (f fb : Fn r) :
    mk (mulOp a * euler v) (-(mulOp b * euler w)) * fnP f fb =
      fnP f fb * mk (mulOp a * euler v) (-(mulOp b * euler w)) + fnP (a * euler v f) (b * euler w fb) := by sorry
