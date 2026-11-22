-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_y_facts
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.y_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:06.08528+00:00
-- url     : https://prove2.me/theorems/0e3f97e6-daba-4184-b817-c8a0d6cc6f82
-- title:
--   S4aux: y facts
-- statement:
--   The S4aux construction uses the y facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L575-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L575-L590

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.y_facts (q ρ : ℕ) (hq : 2 ≤ q) (hρ : 4 ≤ ρ) :
    (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ ∧ 0 ≤ (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
      (q : ℝ) ^ (1 - (ρ : ℤ)) ≤ 1 / 8 := by sorry
