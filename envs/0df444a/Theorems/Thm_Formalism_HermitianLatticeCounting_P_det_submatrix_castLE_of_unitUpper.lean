-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_castLE_of_unitUpper
-- name    : Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitUpper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:49.694388+00:00
-- url     : https://prove2.me/theorems/0ed227fa-3a5b-4c59-85d8-b8aee31a998c
-- title:
--   P: det submatrix cast LE of unit Upper
-- statement:
--   The P construction uses the det submatrix cast LE of unit Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L48-L54

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

theorem Formalism.HermitianLatticeCounting.P.det_submatrix_castLE_of_unitUpper {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (Up : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Up i i = 1) (h0 : ∀ i j, j < i → Up i j = 0) :
    (Up.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by sorry
