-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_geom_eq
-- name    : Formalism.FourierDecayAlt.P.Sz2.geom_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:37.894224+00:00
-- url     : https://prove2.me/theorems/3fb79cd3-fab0-4788-965c-1720c6fc9bf6
-- title:
--   Sz2: geom eq
-- statement:
--   The Sz2 construction uses the geom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L80-L87

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.geom_eq (k d : ℕ) :
    ∑ j ∈ Ioc k (k + d), 1 / (2 : ℝ) ^ j = 1 / 2 ^ k - 1 / 2 ^ (k + d) := by sorry
