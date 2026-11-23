-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_span
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.orth_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:14.405251+00:00
-- url     : https://prove2.me/theorems/e5b2085e-adf2-45d2-8c94-c7ed59d6fdb8
-- title:
--   S4aux: orth span
-- statement:
--   The S4aux construction uses the orth span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3289-L3318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3289-L3318

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
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

theorem Formalism.HermitianLatticeCounting.P.S4aux.orth_span [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Module.Free O (Submodule.span O (Set.range v)) ∧
    Module.finrank O (Submodule.span O (Set.range v)) = Fintype.card κ ∧
    (∀ x, ∃ t ∈ Submodule.span O (Set.range v), ∀ t' ∈ Submodule.span O (Set.range v),
      h (x - t) t' = 0) ∧
    (∀ φ : Submodule.span O (Set.range v) →ₗ[O] O, ∃ w ∈ Submodule.span O (Set.range v),
      ∀ x : Submodule.span O (Set.range v), φ x = h x w) := by sorry
