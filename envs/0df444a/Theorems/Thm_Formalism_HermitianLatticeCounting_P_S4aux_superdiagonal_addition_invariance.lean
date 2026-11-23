-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_superdiagonal_addition_invariance
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.superdiagonal_addition_invariance
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:27.21845+00:00
-- url     : https://prove2.me/theorems/08253af7-38c1-446b-bdbb-33439ff65a91
-- title:
--   S4aux: superdiagonal addition invariance
-- statement:
--   The S4aux construction uses the superdiagonal addition invariance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L215-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L215-L228

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.superdiagonal_addition_invariance : SuperDiagAdd := by sorry
