-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_mul_eq_zero_of_card_lt
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.det_mul_eq_zero_of_card_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:42.405089+00:00
-- url     : https://prove2.me/theorems/851dd762-a19d-4467-aa6d-5a3aae727774
-- title:
--   S4aux: det mul eq zero of card lt
-- statement:
--   The S4aux construction uses the det mul eq zero of card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3132-L3157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3132-L3157

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.det_mul_eq_zero_of_card_lt {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hlt : Fintype.card κ < Fintype.card ι) (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = 0 := by sorry
