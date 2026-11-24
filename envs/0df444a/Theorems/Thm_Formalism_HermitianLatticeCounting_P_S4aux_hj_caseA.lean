-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_caseA
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.hj_caseA
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:40.957803+00:00
-- url     : https://prove2.me/theorems/904477ca-b87b-49cb-92d9-dbcaa7a6da88
-- title:
--   S4aux: hj case A
-- statement:
--   The S4aux construction uses the hj case A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4121-L4218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4121-L4218

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.hj_caseA (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (ω : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ω)
    (hδ : IsUnit (ω - star ω)) (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by sorry
