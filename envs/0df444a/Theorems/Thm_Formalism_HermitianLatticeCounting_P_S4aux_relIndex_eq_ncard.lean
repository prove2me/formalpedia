-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_relIndex_eq_ncard
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.relIndex_eq_ncard
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:36.528974+00:00
-- url     : https://prove2.me/theorems/bc4c8e29-f3f9-445c-8a70-afe195342b9a
-- title:
--   S4aux: rel Index eq ncard
-- statement:
--   The S4aux construction uses the rel Index eq ncard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1096-L1099
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1096-L1099

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.relIndex_eq_ncard (K : Subgroup G) (z : X) :
    (stabilizer G z).relIndex K = (orbit K z).ncard := by sorry
