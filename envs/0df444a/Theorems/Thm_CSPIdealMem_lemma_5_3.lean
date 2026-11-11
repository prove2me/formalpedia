-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_5_3
-- name    : CSPIdealMem.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:48.517281+00:00
-- url     : https://prove2.me/theorems/3fac7bbb-e607-456e-b771-a55b63845128
-- title:
--   Lemma 5.3 — a core retaining the pinned values
-- statement:
--   Let $\Gamma$ be a finite language on a nonempty finite domain $D$. For every $B\subseteq D$ there are a nonempty $A\subseteq D$ with $B\subseteq A$ and a relation-preserving map $r:D\to A$ fixing $A$ pointwise such that the induced structure $\Gamma_B|_A$ is a core (every endomorphism is injective).
--
--   It lets the hardness argument pass to a core without losing the values in $B$.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - reading: "a relation-preserving map r : D → A" → r an endomorphism of Γ_B (it preserves the relations of Γ and the pins b ∈ B), with r(D) ⊆ A; reason: the stronger of the two readings (Γ or Γ_B), and the one the proof constructs
--   - encoding: a finite constraint language Γ (a finite collection of relations R ⊆ D^r) → ConstraintLanguage: relations indexed by a finite type, duplicate names kept (p.10); singleton expansions Γ*, Γ_B add the pins as new indices; reason: Lean convention; duplicate relations change no polymorphism, endomorphism, solution set or complexity
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 5.3, p.34 (PDF 34)

import Mathlib
import Definitions.Def_CSPIdealMem_Polymorphism

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 5.3 (a core retaining the pinned values), p.34 (PDF 34).

For every `B ⊆ D` there are a nonempty `A ⊆ D` containing `B` and a relation-preserving map
`r : D → A` that fixes `A` pointwise, such that the induced structure `Γ_B|A` is a core.

**Formalization Note.** "Relation-preserving" is read for `Γ_B` (the map preserves the relations
of `Γ` and the pins in `B`), the stronger reading, which is what the proof constructs. The domain
is any nonempty finite type `α`. -/
theorem lemma_5_3 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (Γ : ConstraintLanguage α) (B : Finset α) :
    ∃ A : Finset α, A.Nonempty ∧ B ⊆ A ∧
      ∃ r : α → α, IsEndomorphism (Γ.withPins B) r ∧ (∀ a, r a ∈ A) ∧ (∀ a ∈ A, r a = a) ∧
        IsCore ((Γ.withPins B).restrict A) := by sorry

end CSPIdealMem
