-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_injective_fin_le_factorial
-- name    : Formalism.HermitianLatticeCounting.P.card_injective_fin_le_factorial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:37.470221+00:00
-- url     : https://prove2.me/theorems/b7d328f4-906b-4728-93c6-309ea5ea931b
-- title:
--   P: card injective fin le factorial
-- statement:
--   The P construction uses the card injective fin le factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L424-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L424-L432

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.card_injective_fin_le_factorial (t N : ℕ) :
    (Finset.univ.filter (fun f : Fin t → Fin N => Function.Injective f)).card ≤ N.factorial := by sorry
