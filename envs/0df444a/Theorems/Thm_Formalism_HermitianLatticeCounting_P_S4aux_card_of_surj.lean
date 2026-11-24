-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_card_of_surj
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.card_of_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:05.388055+00:00
-- url     : https://prove2.me/theorems/d8720b46-9d37-4db2-b6ec-3fa02683f80d
-- title:
--   S4aux: card of surj
-- statement:
--   The S4aux construction uses the card of surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2241-L2250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2241-L2250

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
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

theorem Formalism.HermitianLatticeCounting.P.S4aux.card_of_surj (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) {G : Type} [AddCommGroup G]
    (f : o →+ G) (hf : Function.Surjective f) (hk : ∀ x, f x = 0 ↔ ϖ ^ i ∣ x) :
    Nat.card G = q ^ i := by sorry
