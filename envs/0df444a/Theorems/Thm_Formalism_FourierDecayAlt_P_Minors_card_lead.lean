-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Minors_card_lead
-- name    : Formalism.FourierDecayAlt.P.Minors.card_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:07.023791+00:00
-- url     : https://prove2.me/theorems/7e2078c6-df20-49b5-920e-bfc626304a78
-- title:
--   Minors: card lead
-- statement:
--   The Minors construction uses the card lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Minors.lean#L152-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Minors.lean#L152-L164

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Minors
open Matrix
variable {K : Type} [Field K]
variable [Fintype K]

theorem Formalism.FourierDecayAlt.P.Minors.card_lead (r : ℕ) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // Lead r C} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by sorry
