-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_exp_mul_of_near_bound
-- name    : Formalism.HermitianLatticeCounting.P.le_exp_mul_of_near_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:39.271873+00:00
-- url     : https://prove2.me/theorems/be6db549-a8e5-4cae-b505-f384cca881e9
-- title:
--   P: le exp mul of near bound
-- statement:
--   The P construction uses the le exp mul of near bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L315-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L315-L344

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset

theorem Formalism.HermitianLatticeCounting.P.le_exp_mul_of_near_bound (N D A δ c : ℝ) (hNA : N ≤ A) (hD : A - δ ≤ D) (hc : 0 < c) (hcA : c ≤ A) (hδ : 0 ≤ δ)
    (h2 : 2 * δ ≤ A) : N ≤ Real.exp (2 * δ / c) * D := by sorry
