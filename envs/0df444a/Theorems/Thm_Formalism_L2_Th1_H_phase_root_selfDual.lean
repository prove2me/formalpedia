-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_phase_root_selfDual
-- name    : Formalism.L2.Th1.H.phase_root_selfDual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:23.972947+00:00
-- url     : https://prove2.me/theorems/4901b020-9b28-423d-ab2a-f8cc3a97b2ee
-- title:
--   H: phase root self Dual
-- statement:
--   The H construction uses the phase root self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/QuadraticSemicharactersOfProductThetaMem.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/QuadraticSemicharactersOfProductThetaMem.lean#L40-L43

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.phase_root_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hΛ : IsSelfDual H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by sorry
