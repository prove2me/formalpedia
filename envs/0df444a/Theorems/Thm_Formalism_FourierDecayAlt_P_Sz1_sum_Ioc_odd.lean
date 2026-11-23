-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_sum_Ioc_odd
-- name    : Formalism.FourierDecayAlt.P.Sz1.sum_Ioc_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:32.348691+00:00
-- url     : https://prove2.me/theorems/3fa4ef54-593a-4f78-ab40-4648fdf28915
-- title:
--   Sz1: sum Ioc odd
-- statement:
--   The Sz1 construction uses the sum Ioc odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L19-L25

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz1.sum_Ioc_odd (k r : ℕ) :
    ∑ M ∈ Ioc k (k + (2 * r + 1)), M = (2 * r + 1) * k + (r + 1) * (2 * r + 1) := by sorry
