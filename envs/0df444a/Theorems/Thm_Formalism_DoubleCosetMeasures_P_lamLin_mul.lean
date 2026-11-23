-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_mul
-- name    : Formalism.DoubleCosetMeasures.P.lamLin_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:01.491819+00:00
-- url     : https://prove2.me/theorems/b28d6df0-0370-47c0-8931-f6c41e66a7d5
-- title:
--   P: lam Lin mul
-- statement:
--   The P construction uses the lam Lin mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L170-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L170-L186

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.DoubleCosetMeasures.P.lamLin_mul (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hup : IsUpUni (B.map R.subtype)) (v : Fin n → R) :
    lamLin R (A.map R.subtype * Z * B.map R.subtype) (A *ᵥ v) = lamLin R Z v := by sorry
