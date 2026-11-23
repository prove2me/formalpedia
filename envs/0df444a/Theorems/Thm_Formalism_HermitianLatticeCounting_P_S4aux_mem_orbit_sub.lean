-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mem_orbit_sub
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.mem_orbit_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:33.548012+00:00
-- url     : https://prove2.me/theorems/3e2ab6cc-938d-494f-9892-3762a3f87565
-- title:
--   S4aux: mem orbit sub
-- statement:
--   The S4aux construction uses the mem orbit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1101-L1104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1101-L1104

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
variable {G X : Type} [Group G] [MulAction G X]
open MulAction

theorem Formalism.HermitianLatticeCounting.P.S4aux.mem_orbit_sub (K : Subgroup G) (z w : X) : w ∈ orbit K z ↔ ∃ k ∈ K, k • z = w := by sorry
