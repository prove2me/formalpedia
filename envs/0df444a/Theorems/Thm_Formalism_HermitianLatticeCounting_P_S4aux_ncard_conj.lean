-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_ncard_conj
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.ncard_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:39.574227+00:00
-- url     : https://prove2.me/theorems/6ec7bb89-1694-4121-9c52-2d87935d6ecb
-- title:
--   S4aux: ncard conj
-- statement:
--   The S4aux construction uses the ncard conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1106-L1120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1106-L1120

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.ncard_conj (g : G) (x y : X) :
    (orbit (stabilizer G (g • y)) x).ncard = (orbit (stabilizer G y) (g⁻¹ • x)).ncard := by sorry
