-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_combine
-- name    : Formalism.FourierDecayAlt.P.Sz4.combine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:09.522715+00:00
-- url     : https://prove2.me/theorems/afbc71b6-a522-433f-9297-2e959b2cf10a
-- title:
--   Sz4: combine
-- statement:
--   The Sz4 construction uses the combine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L640-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L640-L650

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

theorem Formalism.FourierDecayAlt.P.Sz4.combine (E E' C R R' W α β γ M : ℝ) (hE : 0 < E) (hE' : 0 < E') (hC : 0 < C) (hW : 0 < W)
    (hβ : 0 < β) (hM : 0 < M) (h1 : E' ≤ α * E) (h2 : R' ≤ β) (h3 : γ ≤ R)
    (h4 : α * β ≤ M * γ) : E' * C * (R' * W) ≤ M * (E * C * (R * W)) := by sorry
