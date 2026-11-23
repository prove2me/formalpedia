-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_geom_le
-- name    : Formalism.FourierDecayAlt.P.Sz2.geom_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:00.249126+00:00
-- url     : https://prove2.me/theorems/597effa2-520e-484d-9620-dc51755d7314
-- title:
--   Sz2: geom le
-- statement:
--   The Sz2 construction uses the geom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L89-L96

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

theorem Formalism.FourierDecayAlt.P.Sz2.geom_le (k n : ℕ) : ∑ j ∈ Ioc k n, 1 / (2 : ℝ) ^ j ≤ 1 / 2 ^ k := by sorry
