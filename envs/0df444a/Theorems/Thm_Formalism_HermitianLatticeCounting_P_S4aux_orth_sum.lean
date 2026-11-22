-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_sum
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.orth_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:25.283892+00:00
-- url     : https://prove2.me/theorems/29ef6b55-e65d-45f1-a6bf-aa0785b5b3dd
-- title:
--   S4aux: orth sum
-- statement:
--   The S4aux construction uses the orth sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L566-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L566-L573

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.orth_sum {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) :
    (∑ u ∈ univ.filter (fun u => Q u = 0), f u) * (Fintype.card T : ℂ)
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * f u := by sorry
