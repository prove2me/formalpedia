-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_prod_one_sub
-- name    : Formalism.FourierDecayAlt.P.Sz2.prod_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:33.359158+00:00
-- url     : https://prove2.me/theorems/ddaaa1d0-d170-4583-a637-fb2b54620d15
-- title:
--   Sz2: prod one sub
-- statement:
--   The Sz2 construction uses the prod one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L108-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L108-L131

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

theorem Formalism.FourierDecayAlt.P.Sz2.prod_one_sub (q : ℕ) (hq : 2 ≤ q) (k n : ℕ) :
    0 < ∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹) ∧
      |Real.log (∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹))| ≤ 2 / 2 ^ k := by sorry
