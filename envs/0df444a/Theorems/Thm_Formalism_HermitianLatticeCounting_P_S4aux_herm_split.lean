-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_herm_split
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.herm_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:24.768865+00:00
-- url     : https://prove2.me/theorems/eae77161-9e0f-42e7-b4cc-08e6f39043b4
-- title:
--   S4aux: herm split
-- statement:
--   The S4aux construction uses the herm split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1384-L1397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1384-L1397

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.herm_split {E : Type} [CommRing E] [StarRing E] (O : Subring E)
    (htr : ∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) (r : ℕ) (γ : Fin r → Fin r → E)
    (hO : ∀ j k, γ j k ∈ O) (hγ : ∀ j k, star (γ j k) = γ k j) :
    ∃ c : Fin r → Fin r → E, (∀ j k, c j k ∈ O) ∧ ∀ j k, c j k + star (c k j) = γ j k := by sorry
