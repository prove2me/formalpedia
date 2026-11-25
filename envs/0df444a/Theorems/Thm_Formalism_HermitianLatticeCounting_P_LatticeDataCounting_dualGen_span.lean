-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_dualGen_span
-- name    : Formalism.HermitianLatticeCounting.P.LatticeDataCounting.dualGen_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:40.542158+00:00
-- url     : https://prove2.me/theorems/07301331-4c43-448c-9fe2-1dda6a690fad
-- title:
--   Lattice Data Counting: dual Gen span
-- statement:
--   The Lattice Data Counting construction uses the dual Gen span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L240-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean#L240-L298

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
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
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]

theorem Formalism.HermitianLatticeCounting.P.LatticeDataCounting.dualGen_span (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U) (e : ℕ) (s : Fin e → U)
    (hfin : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0)
    (hM : M ≤ N ⊔ Submodule.span (𝓞 E) (Set.range s)) (hs : ∀ i, s i ∈ M) :
    ∃ t : Fin e → U, (∀ i, t i ∈ hdualSub h N) ∧
      hdualSub h N ≤ hdualSub h M ⊔ Submodule.span (𝓞 E) (Set.range t) := by sorry
