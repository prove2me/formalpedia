-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_castLE_of_unitLower
-- name    : Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:45.752918+00:00
-- url     : https://prove2.me/theorems/23a56eab-ae03-4db9-b835-dd278e53bf24
-- title:
--   P: det submatrix cast LE of unit Lower
-- statement:
--   The P construction uses the det submatrix cast LE of unit Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L40-L46

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

theorem Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitLower {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (Lo : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Lo i i = 1) (h0 : ∀ i j, i < j → Lo i j = 0) :
    (Lo.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by sorry
