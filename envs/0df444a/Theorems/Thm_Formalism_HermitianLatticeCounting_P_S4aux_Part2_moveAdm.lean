-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_moveAdm
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.Part2.moveAdm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:24.759078+00:00
-- url     : https://prove2.me/theorems/8d8f0349-576c-44b1-aa37-e01b6bd2bc70
-- title:
--   Part2: move Adm
-- statement:
--   The Part2 construction uses the move Adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1668-L1686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1668-L1686

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2

theorem Formalism.HermitianLatticeCounting.P.S4aux.Part2.moveAdm (H1 : MoveCong) (H2 : EichInv) : MoveAdm := by sorry
