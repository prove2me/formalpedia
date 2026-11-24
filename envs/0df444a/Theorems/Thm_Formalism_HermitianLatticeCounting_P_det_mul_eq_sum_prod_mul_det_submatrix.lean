-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_mul_eq_sum_prod_mul_det_submatrix
-- name    : Formalism.HermitianLatticeCounting.P.det_mul_eq_sum_prod_mul_det_submatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:24.740646+00:00
-- url     : https://prove2.me/theorems/b28a31b5-5399-4a02-bac9-5496d7c98ee7
-- title:
--   P: det mul eq sum prod mul det submatrix
-- statement:
--   The P construction uses the det mul eq sum prod mul det submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L409-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L409-L422

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

theorem Formalism.HermitianLatticeCounting.P.det_mul_eq_sum_prod_mul_det_submatrix {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ) :
    (X * Y).det = ∑ f : Fin t → Fin N, (∏ i, X i (f i)) * (Y.submatrix f id).det := by sorry
