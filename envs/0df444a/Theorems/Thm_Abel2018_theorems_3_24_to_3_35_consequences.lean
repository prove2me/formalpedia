-- Prove2me | Theorems.Thm_Abel2018_theorems_3_24_to_3_35_consequences
-- name    : Abel2018.theorems_3_24_to_3_35_consequences
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:39.991212+00:00
-- url     : https://prove2.me/theorems/21c19099-7b10-48ad-a66a-5a42885316aa
-- title:
--   Metatheoretic Consequences: Constructor Disjointness, Pi-Injectivity, Validity, Normalization, Canonicity, Substitution & Consistency (Theorems 3.24-3.35)
-- statement:
--   Section 3.7 (Theorems 3.24, 3.25, 3.26, 3.28, 3.30, 3.31, 3.32 & 3.35): Full suite of 15 metatheoretic consequences of the fundamental theorem instantiated at the declarative `EqRelSet` instance (`synEqRel`): type constructor disjointness (`U ≠ nat`, `nat ≠ pi`, Theorem 3.24), Pi-type injectivity (Theorem 3.25), syntactic validity for `TypeEq`, `HasType`, and `TermEq` (Theorem 3.26), weak-head normalization for types and terms (Theorem 3.28), canonicity for closed terms of type `nat` (Theorem 3.30), syntactic substitution preservation and congruence across all 4 judgments (Theorem 3.31), substitution composition well-formedness (Theorem 3.32), and Peano disjointness `¬ TermEq Γ .zero (.succ n) .nat` in arbitrary contexts `Γ` (Theorem 3.35).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 3.7 (Theorems 3.24, 3.25, 3.26, 3.28, 3.30, 3.31, 3.32, and 3.35; `Consequences.agda` and ` Substitution.agda`).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem theorems_3_24_to_3_35_consequences :
    (∀ {Γ : Context}, ¬ TypeEq Γ .univ .nat) ∧
    (∀ {Γ : Context} {F G : Term}, ¬ TypeEq Γ .nat (.pi F G)) ∧
    (∀ {Γ : Context} {F G H E : Term}, TypeEq Γ (.pi F G) (.pi H E) →
      TypeEq Γ F H ∧ TypeEq (F :: Γ) G E) ∧
    (∀ {Γ : Context} {A B : Term}, TypeEq Γ A B →
      TypeWf Γ A ∧ TypeWf Γ B) ∧
    (∀ {Γ : Context} {t A : Term}, HasType Γ t A →
      TypeWf Γ A) ∧
    (∀ {Γ : Context} {t u A : Term}, TermEq Γ t u A →
      TypeWf Γ A ∧ HasType Γ t A ∧ HasType Γ u A) ∧
    (∀ {Γ : Context} {A : Term}, TypeWf Γ A →
      ∃ B, Whnf B ∧ TypeStarWf Γ A B) ∧
    (∀ {Γ : Context} {a A : Term}, HasType Γ a A →
      ∃ b, Whnf b ∧ StarWf Γ a b A) ∧
    (∀ {t : Term}, HasType [] t .nat →
      ∃ k, TermEq [] t (suck k) .nat) ∧
    (∀ {Γ Δ : Context} {A : Term} {σ : Subst},
      TypeWf Γ A → SubstWf Δ σ Γ → CtxWf Δ →
      TypeWf Δ (subst σ A)) ∧
    (∀ {Γ Δ : Context} {A B : Term} {σ σ' : Subst},
      TypeEq Γ A B → SubstEq Δ σ σ' Γ → CtxWf Δ →
      TypeEq Δ (subst σ A) (subst σ' B)) ∧
    (∀ {Γ Δ : Context} {t A : Term} {σ : Subst},
      HasType Γ t A → SubstWf Δ σ Γ → CtxWf Δ →
      HasType Δ (subst σ t) (subst σ A)) ∧
    (∀ {Γ Δ : Context} {t u A : Term} {σ σ' : Subst},
      TermEq Γ t u A → SubstEq Δ σ σ' Γ → CtxWf Δ →
      TermEq Δ (subst σ t) (subst σ' u) (subst σ A)) ∧
    (∀ {σ σ' : Subst} {Γ Δ Δ' : Context},
      CtxWf Γ → CtxWf Δ → CtxWf Δ' →
      SubstWf Δ' σ Δ → SubstWf Δ σ' Γ →
      SubstWf Δ' (compSubst σ σ') Γ) ∧
    (∀ {Γ : Context} {n : Term},
      ¬ TermEq Γ .zero (.succ n) .nat) := by sorry

end Abel2018
