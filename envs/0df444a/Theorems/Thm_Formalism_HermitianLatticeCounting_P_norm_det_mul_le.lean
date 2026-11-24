-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_mul_le
-- name    : Formalism.HermitianLatticeCounting.P.norm_det_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:23.395685+00:00
-- url     : https://prove2.me/theorems/16a98557-a887-4116-9bbc-90cd9b178be0
-- title:
--   P: norm det mul le
-- statement:
--   The P construction uses the norm det mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L434-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L434-L462

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

theorem Formalism.HermitianLatticeCounting.P.norm_det_mul_le {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ)
    (ρ Q : ℝ) (hρ : 1 ≤ ρ) (hQ : 0 ≤ Q) (hX : ∀ i k, ‖X i k‖ ≤ ρ)
    (hY : ∀ f : Fin t → Fin N, ‖(Y.submatrix f id).det‖ ≤ Q) :
    ‖(X * Y).det‖ ≤ (N.factorial : ℝ) * ρ ^ N * Q := by sorry
