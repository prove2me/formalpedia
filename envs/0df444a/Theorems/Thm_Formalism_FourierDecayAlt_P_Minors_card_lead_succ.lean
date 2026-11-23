-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Minors_card_lead_succ
-- name    : Formalism.FourierDecayAlt.P.Minors.card_lead_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:16.8591+00:00
-- url     : https://prove2.me/theorems/c86d35a7-f35e-4c1e-8451-4091687a9c9e
-- title:
--   Minors: card lead succ
-- statement:
--   The Minors construction uses the card lead succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Minors.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Minors.lean#L132-L140

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

theorem Formalism.FourierDecayAlt.P.Minors.card_lead_succ (r : ℕ) :
    Nat.card {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} =
      Nat.card {A : Matrix (Fin r) (Fin r) K // Lead r A} *
        (Fintype.card K ^ r * (Fintype.card K ^ r * (Fintype.card K - 1))) := by sorry
