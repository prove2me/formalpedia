-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fiber_sum
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.fiber_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:18.234102+00:00
-- url     : https://prove2.me/theorems/48c1cf61-f984-4095-8d2f-7c1d7a5fba45
-- title:
--   S4aux: fiber sum
-- statement:
--   The S4aux construction uses the fiber sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1124-L1136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L1124-L1136

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.fiber_sum {X : Type} (A B : Finset X) (R : X → X → Prop) [∀ z, DecidablePred (R z)] (F : X → ℝ)
    (nb : X → ℕ) (h1 : ∀ z ∈ A, ∃ z' ∈ B, R z z')
    (h2 : ∀ z ∈ A, ∀ z' ∈ B, R z z' → (B.filter (R z)).card = nb z') :
    ∑ z ∈ A, F z = ∑ z ∈ A, ∑ z' ∈ B.filter (R z), F z / nb z' := by sorry
