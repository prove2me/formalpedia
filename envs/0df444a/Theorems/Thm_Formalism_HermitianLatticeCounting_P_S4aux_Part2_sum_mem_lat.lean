-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_sum_mem_lat
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.Part2.sum_mem_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:39.896978+00:00
-- url     : https://prove2.me/theorems/3b99ea20-4ec2-4c5e-8644-0580e67d74f5
-- title:
--   Part2: sum mem lat
-- statement:
--   The Part2 construction uses the sum mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1590-L1592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1590-L1592

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.Part2.sum_mem_lat {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {abelian₂ : AddSubgroup V}
    (hL : IsLat O abelian₂) {n : ℕ} {f : Fin n → V} {a : Fin n → E} (hf : ∀ i, f i ∈ abelian₂) (ha : ∀ i, a i ∈ O) :
    (∑ i, a i • f i) ∈ abelian₂ := by sorry
