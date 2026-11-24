-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_primepow_dvd
-- name    : Formalism.HermitianLatticeCounting.P.prod_primepow_dvd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:54.629806+00:00
-- url     : https://prove2.me/theorems/9de3080a-c056-42a4-a4d0-ebe7ac1a225f
-- title:
--   P: prod primepow dvd
-- statement:
--   The P construction uses the prod primepow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L84-L97

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.prod_primepow_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) (n : ℕ)
    (h : ∀ p ∈ s, p ^ e p ∣ n) : ∏ p ∈ s, p ^ e p ∣ n := by sorry
