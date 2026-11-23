-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_half
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.geo_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:01.397035+00:00
-- url     : https://prove2.me/theorems/5f334b5d-9dcf-4b68-8ead-ebc7a29d3e23
-- title:
--   S4aux: geo half
-- statement:
--   The S4aux construction uses the geo half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L545-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L545-L551

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.geo_half (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (N : ℕ) : ∑ l ∈ range N, y ^ l ≤ 2 - 2 * y ^ N := by sorry
