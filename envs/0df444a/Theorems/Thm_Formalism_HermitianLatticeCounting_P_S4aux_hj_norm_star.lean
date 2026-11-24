-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_norm_star
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hj_norm_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:38.299804+00:00
-- url     : https://prove2.me/theorems/bdae41ed-3d7a-4154-9b3e-276e89ed79c0
-- title:
--   S4aux: hj norm star
-- statement:
--   The S4aux construction uses the hj norm star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4067-L4079
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4067-L4079

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hj_norm_star (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (x : E) : algebraMap F E (Algebra.norm F x) = x * star x := by sorry
