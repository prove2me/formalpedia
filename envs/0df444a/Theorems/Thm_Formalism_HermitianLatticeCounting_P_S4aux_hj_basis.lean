-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_basis
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hj_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:19.610925+00:00
-- url     : https://prove2.me/theorems/6e87bedb-c163-45c8-abd4-5c58b35135c1
-- title:
--   S4aux: hj basis
-- statement:
--   The S4aux construction uses the hj basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4018-L4037
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4018-L4037

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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E]

theorem Formalism.HermitianLatticeCounting.P.S4aux.hj_basis (h2 : Module.finrank F E = 2) (ω : E) (hω : ∀ c : F, algebraMap F E c ≠ ω) :
    ∃ β : Module.Basis (Fin 2) F E, β 0 = 1 ∧ β 1 = ω := by sorry
