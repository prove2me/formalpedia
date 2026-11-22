-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_one
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.unram_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:27.146858+00:00
-- url     : https://prove2.me/theorems/7bc28edf-52fa-4244-af5c-23bcf7cfe95d
-- title:
--   S4aux: unram one
-- statement:
--   The S4aux construction uses the unram one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1252-L1279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1252-L1279

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

theorem Formalism.HermitianLatticeCounting.P.S4aux.unram_one (hU : Unram o O) : ∃ l : O →ₗ[o] o, l 1 = 1 := by sorry
