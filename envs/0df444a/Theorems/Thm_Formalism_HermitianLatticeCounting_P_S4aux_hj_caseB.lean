-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_caseB
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hj_caseB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:36.237393+00:00
-- url     : https://prove2.me/theorems/c1ff7445-3b3f-4a67-b6d9-e4403ad629fc
-- title:
--   S4aux: hj case B
-- statement:
--   The S4aux construction uses the hj case B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4258-L4427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4258-L4427

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hj_caseB (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (ε : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ε)
    (hε : ε * ε = 0) (hstar : star ε = -ε) (htwo : (2 : F) ≠ 0) (m : ℕ)
    (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by sorry
