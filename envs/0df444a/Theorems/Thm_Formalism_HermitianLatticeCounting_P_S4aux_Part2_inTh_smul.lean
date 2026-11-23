-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_smul
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:35.95581+00:00
-- url     : https://prove2.me/theorems/5cfb1dfd-35c0-4b32-95e3-79d5f44adc81
-- title:
--   Part2: in Th smul
-- statement:
--   The Part2 construction uses the in Th smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1565-L1568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1565-L1568

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_smul {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {th c : E}
    {abelian₂ : AddSubgroup V} {a : V} (hL : IsLat O abelian₂) (hc : c ∈ O) (ha : InTh th abelian₂ a) : InTh th abelian₂ (c • a) := by sorry
