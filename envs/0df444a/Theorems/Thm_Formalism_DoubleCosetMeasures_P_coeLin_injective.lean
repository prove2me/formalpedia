-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_coeLin_injective
-- name    : Formalism.DoubleCosetMeasures.P.coeLin_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:53.957076+00:00
-- url     : https://prove2.me/theorems/cbc2dde2-3255-49e3-a088-c67374fdf067
-- title:
--   P: coe Lin injective
-- statement:
--   The P construction uses the coe Lin injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LowUniMulVecELast.lean#L28-L33

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

theorem Formalism.DoubleCosetMeasures.P.coeLin_injective : Function.Injective (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)) := by sorry
