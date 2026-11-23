-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_ls_ext
-- name    : Formalism.FourierDecayAlt.P.TA1.ls_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:29.774429+00:00
-- url     : https://prove2.me/theorems/0a3745f3-f63c-446a-8773-5d8a252f2b0c
-- title:
--   TA1: ls ext
-- statement:
--   The TA1 construction uses the ls ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L74-L75

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]
omit [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.TA1.ls_ext (h : Pt E) (s : ℕ) (t : E) : ls (Formalism.FourierDecayAlt.TA.ext h s t) = s := by sorry
