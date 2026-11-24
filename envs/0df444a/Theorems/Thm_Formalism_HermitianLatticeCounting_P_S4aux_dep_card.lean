-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dep_card
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.dep_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:08.823818+00:00
-- url     : https://prove2.me/theorems/1c4f4bba-9c68-4972-bae6-247488a8f7c4
-- title:
--   S4aux: dep card
-- statement:
--   The S4aux construction uses the dep card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2391-L2420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2391-L2420

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.dep_card [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card * c
      ≤ Fintype.card F ^ m * c ^ m := by sorry
