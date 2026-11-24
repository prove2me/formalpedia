-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_neg
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:05.599398+00:00
-- url     : https://prove2.me/theorems/2264324c-1e65-4235-ad0a-fb1fad08ecbc
-- title:
--   Part2: in Th neg
-- statement:
--   The Part2 construction uses the in Th neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1570-L1573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1570-L1573

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_neg {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a : V}
    (ha : InTh th abelian₂ a) : InTh th abelian₂ (-a) := by sorry
