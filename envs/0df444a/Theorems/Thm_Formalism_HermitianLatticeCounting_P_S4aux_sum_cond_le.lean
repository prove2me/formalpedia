-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_sum_cond_le
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.sum_cond_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:30.626569+00:00
-- url     : https://prove2.me/theorems/5d1dbda4-888b-4c7a-b033-b20f47c40284
-- title:
--   S4aux: sum cond le
-- statement:
--   The S4aux construction uses the sum cond le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L553-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L553-L564

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.sum_cond_le {Ψ : Type*} [Fintype Ψ] (cond : Ψ → ℕ) (g B : ℕ → ℝ)
    (hb : ∀ i, ((univ.filter fun ψ => cond ψ = i).card : ℝ) * g i ≤ B i) :
    ∃ N, ∀ N' ≥ N, ∑ ψ, g (cond ψ) ≤ ∑ i ∈ range N', B i := by sorry
