-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_injective_pos_bounds
-- name    : Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_pos_bounds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:41.921515+00:00
-- url     : https://prove2.me/theorems/90b1ae02-f9e8-4dc0-8d73-ff3893d68da0
-- title:
--   P: prod succ div injective pos bounds
-- statement:
--   The P construction uses the prod succ div injective pos bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L85-L102

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

theorem Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_pos_bounds {ι : Type} (I : Finset ι) (y : ι → ℕ) (hinj : Set.InjOn y (I : Set ι)) (h1 : ∀ i ∈ I, 1 ≤ y i) :
    1 ≤ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ∧ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ≤ (I.card : ℝ) + 1 := by sorry
