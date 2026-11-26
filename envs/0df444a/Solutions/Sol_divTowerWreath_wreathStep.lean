-- Prove2me | solution 1 for divTowerWreath_wreathStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:32.17533+00:00
-- url     : https://prove2.me/submissions/5dd9517d-cb81-4762-94e2-700a49419f63

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
public import Theorems.Thm_sgDiv_refl
public import Theorems.Thm_divTowerWreath_cons
public import Theorems.Thm_divTowerWreath_of_sgDiv
public import Theorems.Thm_sgDiv_wreath_assoc
public import Theorems.Thm_sgDiv_wreath_decoration_mono
public import Theorems.Thm_subsingleton_of_sgDiv_punit
public import Theorems.Thm_sgDiv_wreath_of_subsingleton_decoration
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
public import Theorems.Thm_KrohnRhodes_sgDiv_trans
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
theorem _root_.solution :
    ∀ (towA : List KRFactor.{u}) {S A B X : Type u}
      [Monoid S] [Finite S] [Monoid A] [Finite A] [Monoid B] [Finite B]
      [Fintype X] [MulAction B X],
      SgDiv S (WreathProduct A B X) → DivTowerWreath A towA →
      ∀ {towB : List KRFactor.{u}}, DivTowerWreath B towB →
        DivTowerWreath S (towA ++ towB) := by
  intro towA
  induction towA with
  | nil =>
      intro S A B X _ _ _ _ _ _ _ _ hdiv hA towB hB
      rw [divTowerWreath_nil] at hA
      have : Subsingleton A := subsingleton_of_sgDiv_punit A hA
      have hSB : SgDiv S B :=
        KrohnRhodes.sgDiv_trans hdiv
          (sgDiv_wreath_of_subsingleton_decoration A B X)
      simpa using divTowerWreath_of_sgDiv hSB hB
  | cons F rest IH =>
      intro S A B X _ _ _ _ _ _ _ _ hdiv hA towB hB
      rw [divTowerWreath_cons] at hA
      obtain ⟨B', mB', fB', Y', fY', aY', hB'rest, hAdiv⟩ := hA
      rw [List.cons_append, divTowerWreath_cons]
      -- The new base is the wreath `B' ≀_X B` (using the *outer* state `X`), acting
      -- on the product state `Y' × X` via `WreathAssoc.actW`.
      have : Fintype B' := Fintype.ofFinite B'
      let := WreathAssoc.actW B' B Y' X
      refine ⟨WreathProduct B' B X, inferInstance, inferInstance,
        Y' × X, inferInstance, WreathAssoc.actW B' B Y' X, ?_, ?_⟩
      · -- The base `B' ≀_X B` decomposes via `rest ++ towB` by the IH at `rest`:
        -- `B' ≀_X B  ≼  B' ≀_X B` (reflexivity), `B'` decomposes via `rest`,
        -- `B` via `towB`.
        exact IH (S := WreathProduct B' B X) (A := B') (B := B) (X := X)
          (sgDiv_refl _) hB'rest hB
      · -- The head SgDiv: push `A ≼ F.carrier ≀_{Y'} B'` into the decoration, then
        -- re-associate `(F.carrier ≀_{Y'} B') ≀_X B  ≼  F.carrier ≀_{Y' × X} (B' ≀_X B)`.
        have h1 : SgDiv (WreathProduct A B X)
            (WreathProduct (WreathProduct F.carrier B' Y') B X) :=
          sgDiv_wreath_decoration_mono A (WreathProduct F.carrier B' Y') B X hAdiv
        have h2 : SgDiv (WreathProduct (WreathProduct F.carrier B' Y') B X)
            (WreathProduct F.carrier (WreathProduct B' B X) (Y' × X)) :=
          sgDiv_wreath_assoc F.carrier B' B Y' X
        exact KrohnRhodes.sgDiv_trans hdiv
          (KrohnRhodes.sgDiv_trans h1 h2)
