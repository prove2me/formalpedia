-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_congrE
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.det_congrE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:20.661752+00:00
-- url     : https://prove2.me/theorems/d74f4478-c606-4e95-bb89-cdb1cf539669
-- title:
--   S4aux: det congr E
-- statement:
--   The S4aux construction uses the det congr E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4112-L4114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4112-L4114

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {E : Type} [CommRing E]

theorem Formalism.HermitianLatticeCounting.P.S4aux.det_congrE [StarRing E] (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulE m A ∘ₗ lmulE m A.conjTranspose) = (A.det * star A.det) ^ m := by sorry
