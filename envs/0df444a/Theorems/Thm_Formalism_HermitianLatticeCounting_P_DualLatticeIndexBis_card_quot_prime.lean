-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_card_quot_prime
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.card_quot_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:06.454683+00:00
-- url     : https://prove2.me/theorems/26669a40-6404-4f83-a010-32d5bc05e71c
-- title:
--   Dual Lattice Index Bis: card quot prime
-- statement:
--   The Dual Lattice Index Bis construction uses the card quot prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L608-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L608-L623

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
open TensorProduct

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.card_quot_prime {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by sorry
