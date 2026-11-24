-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_dual_key
-- name    : Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.dual_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:42.8071+00:00
-- url     : https://prove2.me/theorems/dc970f93-ad62-461e-8a5d-2a39e5a70dd3
-- title:
--   Dual Lattice Index Bis: dual key
-- statement:
--   The Dual Lattice Index Bis construction uses the dual key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L958-L990
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ColonCountWeighted.lean#L958-L990

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
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]

theorem Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.dual_key (h : U →ₗ[E] U →ₗ⋆[E] E) (δ : 𝓞 E) (K : Ideal (𝓞 E))
    (hcod : ∀ z : E, (∃ o : 𝓞 E, (o : E) = (δ : E) * z) ↔
        ∀ a ∈ K, ∃ n : ℤ, Algebra.trace ℚ E (star (a : E) * z) = n)
    (L : Submodule (𝓞 E) U) (x : U) :
    ((δ : E) • x ∈ hdual h (algebraMap (𝓞 E) E).range L.toAddSubgroup) ↔
        ∀ y ∈ K • L, ∃ n : ℤ, trForm h x y = n := by sorry
