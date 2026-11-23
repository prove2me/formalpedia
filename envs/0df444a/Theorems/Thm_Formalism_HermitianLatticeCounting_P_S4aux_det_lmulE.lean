-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_lmulE
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.det_lmulE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:50.076915+00:00
-- url     : https://prove2.me/theorems/752896b6-7577-4088-92ae-98996d7c6d99
-- title:
--   S4aux: det lmul E
-- statement:
--   The S4aux construction uses the det lmul E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4101-L4110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4101-L4110

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.det_lmulE (m : ℕ) (B : Matrix (Fin m) (Fin m) E) : LinearMap.det (lmulE m B) = B.det ^ m := by sorry
