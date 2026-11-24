-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dep_one
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.dep_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:13.324635+00:00
-- url     : https://prove2.me/theorems/f92fa9d8-11f0-469f-a85a-2ee6c12a380c
-- title:
--   S4aux: dep one
-- statement:
--   The S4aux construction uses the dep one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2345-L2389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2345-L2389

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.dep_one [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (lam : Fin m → F) (j0 : Fin m) (hj0 : lam j0 ≠ 0) :
    ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c ≤ c ^ m := by sorry
