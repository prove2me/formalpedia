-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_geo_q
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.geo_q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:08.65243+00:00
-- url     : https://prove2.me/theorems/8badd81e-8340-4e02-8048-756d631e15e5
-- title:
--   S4aux: geo q
-- statement:
--   The S4aux construction uses the geo q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L680-L686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L680-L686

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.geo_q (q : ℝ) (hq : 2 ≤ q) (j : ℕ) : ∑ i ∈ range (j + 1), q ^ i ≤ 2 * q ^ j - 1 := by sorry
