-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_density_arith
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.density_arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:17.251606+00:00
-- url     : https://prove2.me/theorems/7b09d9b7-3680-4d4a-8f88-88fc6471c887
-- title:
--   S4aux: density arith
-- statement:
--   The S4aux construction uses the density arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2449-L2507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2449-L2507

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.density_arith (Q : ℝ) (hQ : 2 ≤ Q) (n m : ℕ) (hn : 2 * m + 3 ≤ n) (c NX tot : ℝ)
    (hc : c * Q ^ m = Q ^ n)
    (hX1 : NX ≤ (Q ^ n) ^ m) (hX2 : (Q ^ n) ^ m - Q ^ m * (Q ^ n) ^ m / Q ^ n ≤ NX)
    (ht1 : tot ≤ NX * c ^ m) (ht2 : NX * (c ^ m - Q ^ m * c ^ m / c) ≤ tot) :
    Q ^ (2 * n * m) / Q ^ (m ^ 2) / 2 ≤ tot ∧ tot ≤ 2 * (Q ^ (2 * n * m) / Q ^ (m ^ 2)) := by sorry
