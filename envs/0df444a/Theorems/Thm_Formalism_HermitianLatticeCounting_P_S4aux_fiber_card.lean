-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fiber_card
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.fiber_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:51.081803+00:00
-- url     : https://prove2.me/theorems/4124faa6-069c-4ee4-b8e2-666853395216
-- title:
--   S4aux: fiber card
-- statement:
--   The S4aux construction uses the fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2332-L2343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2332-L2343

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
variable {F : Type} [Field F] [Fintype F]

theorem Formalism.HermitianLatticeCounting.P.S4aux.fiber_card [DecidableEq F] {j n : ℕ} (M : Matrix (Fin j) (Fin n) F)
    (hM : LinearIndependent F M.row) (g : Fin j → F) :
    (univ.filter fun y : Fin n → F => M.mulVec y = g).card * Fintype.card F ^ j
      = Fintype.card F ^ n := by sorry
