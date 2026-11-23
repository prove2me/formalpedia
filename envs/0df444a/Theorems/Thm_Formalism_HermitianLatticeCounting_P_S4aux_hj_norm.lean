-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_norm
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hj_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:14.699079+00:00
-- url     : https://prove2.me/theorems/6a800129-3a77-4e12-b335-7aeb6c954a04
-- title:
--   S4aux: hj norm
-- statement:
--   The S4aux construction uses the hj norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4054-L4065
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4054-L4065

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hj_norm (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (t nn : F)
    (hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn) (a b : F) :
    Algebra.norm F (algebraMap F E a + algebraMap F E b * ω) = a ^ 2 + a * b * t + b ^ 2 * nn := by sorry
