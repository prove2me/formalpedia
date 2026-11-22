-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply
-- name    : Formalism.DoubleCosetMeasures.P.lamLin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:21.087251+00:00
-- url     : https://prove2.me/theorems/ad6fbd91-3732-4938-934a-47d681d937c6
-- title:
--   P: lam Lin apply
-- statement:
--   The P construction uses the lam Lin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L101-L102

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

theorem Formalism.DoubleCosetMeasures.P.lamLin_apply (Z : Matrix (Fin n) (Fin n) K) (v : Fin n → R) :
    lamLin R Z v = Submodule.mkQ _ (lastCoord R (Z⁻¹ *ᵥ coeLin R v)) := by sorry
