-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_injective_int_bounds
-- name    : Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_int_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:35.773265+00:00
-- url     : https://prove2.me/theorems/8536a2f9-acfd-4c00-9250-dd98581a9219
-- title:
--   P: prod succ div injective int bounds
-- statement:
--   The P construction uses the prod succ div injective int bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L104-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CircleIntegralInvSubEqZeroOfOutside.lean#L104-L188

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

theorem Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_int_bounds {ι : Type} (I : Finset ι) (x : ι → ℤ) (hinj : Set.InjOn x (I : Set ι)) (h0 : ∀ i ∈ I, x i ≠ 0)
    (h1 : ∀ i ∈ I, x i ≠ -1) :
    1 / ((I.card : ℝ) + 1) ≤ ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ∧
      ∏ i ∈ I, (((x i : ℝ) + 1) / (x i : ℝ)) ≤ (I.card : ℝ) + 1 := by sorry
