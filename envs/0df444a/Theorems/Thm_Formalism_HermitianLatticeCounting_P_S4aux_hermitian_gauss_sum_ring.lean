-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_gauss_sum_ring
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hermitian_gauss_sum_ring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:58.536124+00:00
-- url     : https://prove2.me/theorems/a61000ee-1266-4de8-9095-c4e13dab5b5e
-- title:
--   S4aux: hermitian gauss sum ring
-- statement:
--   The S4aux construction uses the hermitian gauss sum ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L926-L1012
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L926-L1012

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hermitian_gauss_sum_ring : HermGaussRing := by sorry
