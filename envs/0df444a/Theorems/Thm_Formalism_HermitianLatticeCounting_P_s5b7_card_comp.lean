-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_card_comp
-- name    : Formalism.HermitianLatticeCounting.P.s5b7_card_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:04.747515+00:00
-- url     : https://prove2.me/theorems/a92a02f8-5b46-4035-90ac-45c4b1a5a269
-- title:
--   P: s5b7 card comp
-- statement:
--   The P construction uses the s5b7 card comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L9-L29

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module

theorem Formalism.HermitianLatticeCounting.P.s5b7_card_comp {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Injective g) :
    Nat.card (C ⧸ LinearMap.range (g ∘ₗ f)) =
      Nat.card (B ⧸ LinearMap.range f) * Nat.card (C ⧸ LinearMap.range g) := by sorry
