-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_norm_surj
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.norm_surj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:37.594682+00:00
-- url     : https://prove2.me/theorems/0c564ec7-0e06-4b6e-8768-a3e08c59dfc4
-- title:
--   S4aux: norm surj
-- statement:
--   The S4aux construction uses the norm surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3892-L3923
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3892-L3923

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

theorem Formalism.HermitianLatticeCounting.P.S4aux.norm_surj (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (ha : a ^ Fintype.card K = a) : ∃ lam : L, lam ^ (Fintype.card K + 1) = a := by sorry
