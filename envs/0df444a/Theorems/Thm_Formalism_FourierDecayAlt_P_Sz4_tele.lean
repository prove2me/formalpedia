-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_tele
-- name    : Formalism.FourierDecayAlt.P.Sz4.tele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:30.83007+00:00
-- url     : https://prove2.me/theorems/7f67e7ef-fcc7-4c87-8577-ca40776c54cf
-- title:
--   Sz4: tele
-- statement:
--   The Sz4 construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L25-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.tele (g : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Icc 1 n, (g (i + 1) - g i) = g (n + 1) - g 1 := by sorry
