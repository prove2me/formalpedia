-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_term_le
-- name    : Formalism.FourierDecayAlt.P.Sz2.term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:30.513809+00:00
-- url     : https://prove2.me/theorems/f180a331-6385-48c9-b11e-0711841aa518
-- title:
--   Sz2: term le
-- statement:
--   The Sz2 construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L8-L23

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

theorem Formalism.FourierDecayAlt.P.Sz2.term_le (M N : ℕ) (hM : 3 ≤ M) (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ^ M ≤
      4 / 2 ^ M * (1 / ((N : ℝ) * (N + 1)) - 1 / (((N : ℝ) + 1) * (N + 2))) := by sorry
