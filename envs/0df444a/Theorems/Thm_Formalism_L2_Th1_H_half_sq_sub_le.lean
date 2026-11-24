-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_half_sq_sub_le
-- name    : Formalism.L2.Th1.H.half_sq_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:17.23951+00:00
-- url     : https://prove2.me/theorems/b7b71e7b-5b87-4800-a9c9-519e92d082cb
-- title:
--   H: half sq sub le
-- statement:
--   The H construction uses the half sq sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L17-L25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.half_sq_sub_le {V : Type*} [NormedAddCommGroup V] (x z₀ : V) :
    ‖x‖ ^ 2 / 2 - ‖z₀‖ ^ 2 ≤ ‖x - z₀‖ ^ 2 := by sorry
