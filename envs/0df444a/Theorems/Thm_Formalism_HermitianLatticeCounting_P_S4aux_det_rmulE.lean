-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_rmulE
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.det_rmulE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:42.536519+00:00
-- url     : https://prove2.me/theorems/ea4aa503-058f-4d67-9494-45c7d6ba0bdc
-- title:
--   S4aux: det rmul E
-- statement:
--   The S4aux construction uses the det rmul E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4098-L4099
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4098-L4099

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.det_rmulE (m : ℕ) (A : Matrix (Fin m) (Fin m) E) : LinearMap.det (rmulE m A) = A.det ^ m := by sorry
