-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_span_pow
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.index_span_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:08.567266+00:00
-- url     : https://prove2.me/theorems/07908752-f564-4111-aab1-5b36addf2f51
-- title:
--   S4aux: index span pow
-- statement:
--   The S4aux construction uses the index span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2230-L2239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2230-L2239

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
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

theorem Formalism.HermitianLatticeCounting.P.S4aux.index_span_pow (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) :
    (Ideal.span {ϖ ^ i}).toAddSubgroup.index = q ^ i := by sorry
