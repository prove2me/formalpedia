-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_step_arith
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.step_arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:25.64994+00:00
-- url     : https://prove2.me/theorems/0dd80efd-52e5-4c77-970d-651db3f6726e
-- title:
--   S4aux: step arith
-- statement:
--   The S4aux construction uses the step arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2905-L2962
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2905-L2962

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.step_arith (q N a W Qj Cj C' lo hi : ℝ) (hq : 2 ≤ q) (hN : 0 < N) (ha : 0 < a)
    (hWa : W * a = N ^ 2) (hsmall : q ^ 2 * a * 8 ≤ N) (hQ : 0 ≤ Qj)
    (h1 : (1 - a / N) * Qj ≤ Cj) (h2 : Cj ≤ (1 + a / N) * Qj)
    (hlo : lo = (W - q * N - q * a) / q) (hhi : hi = (W + q * N) / q)
    (hC1 : Cj * lo ≤ C') (hC2 : C' ≤ Cj * hi) :
    (1 - q ^ 2 * a / N) * (Qj * W / q) ≤ C' ∧ C' ≤ (1 + q ^ 2 * a / N) * (Qj * W / q) := by sorry
