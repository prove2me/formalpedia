-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_surj
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.trace_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:56.206797+00:00
-- url     : https://prove2.me/theorems/a7a4e6a6-47fc-48e2-9de0-420bc4a6eb64
-- title:
--   S4aux: trace surj
-- statement:
--   The S4aux construction uses the trace surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2637-L2639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2637-L2639

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.trace_surj : Function.Surjective (Algebra.trace K L) := by sorry
