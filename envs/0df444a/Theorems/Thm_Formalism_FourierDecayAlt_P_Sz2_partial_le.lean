-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_partial_le
-- name    : Formalism.FourierDecayAlt.P.Sz2.partial_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:31.027899+00:00
-- url     : https://prove2.me/theorems/9fc0d0f9-de53-4051-8a41-22acc5ec9a09
-- title:
--   Sz2: partial le
-- statement:
--   The Sz2 construction uses the partial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L25-L45

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

theorem Formalism.FourierDecayAlt.P.Sz2.partial_le (M : ℕ) (hM : 3 ≤ M) (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((i : ℝ) + 1) ^ M ≤
      1 + 2 / 2 ^ M - 4 / 2 ^ M * (1 / (((n : ℝ) + 1) * (n + 2))) := by sorry
