-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_piO
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.index_piO
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:41.608752+00:00
-- url     : https://prove2.me/theorems/4756a7c1-3c10-457f-b06f-03283ea488a7
-- title:
--   S4aux: index pi O
-- statement:
--   The S4aux construction uses the index pi O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3754-L3801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3754-L3801

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

theorem Formalism.HermitianLatticeCounting.P.S4aux.index_piO (hU : Unram o O) (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (M : ℕ) : (piO O ϖ M).index = q ^ (2 * M) := by sorry
