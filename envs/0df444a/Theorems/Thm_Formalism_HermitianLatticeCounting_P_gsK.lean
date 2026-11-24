-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gsK
-- name    : Formalism.HermitianLatticeCounting.P.gsK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:36.146019+00:00
-- url     : https://prove2.me/theorems/cc288d4b-aa34-440c-a077-b554f88e1516
-- title:
--   P: gs K
-- statement:
--   The P construction uses the gs K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L401-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L401-L456

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
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
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]

theorem Formalism.HermitianLatticeCounting.P.gsK (h : U →ₗ[K] U →ₗ⋆[K] K) (herm : ∀ x y : U, star (h x y) = h y x)
    (haniso : ∀ x : U, h x x = 0 → x = 0) :
    ∀ (s : ℕ) (w : Fin s → U), ∃ (g : Fin s → U) (L : Matrix (Fin s) (Fin s) K), L.det = 1 ∧
      (∀ b, w b = ∑ c, L b c • g c) ∧ (∀ a b, a ≠ b → h (g a) (g b) = 0) := by sorry
