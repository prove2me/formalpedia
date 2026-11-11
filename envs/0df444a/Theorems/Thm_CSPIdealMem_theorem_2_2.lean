-- Prove2me | Theorems.Thm_CSPIdealMem_theorem_2_2
-- name    : CSPIdealMem.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:38.434421+00:00
-- url     : https://prove2.me/theorems/70faa9b9-f20c-4999-a64a-03f3202c7209
-- title:
--   Theorem 2.2 — cyclic polymorphisms of every prime arity $p>|D|$ (Barto–Kozik, cited)
-- statement:
--   Let $\Gamma$ be a finite constraint language on a nonempty finite domain $D$. If the singleton expansion $\Gamma^*$ has a Taylor polymorphism, then for every prime $p>|D|$ it has an idempotent cyclic polymorphism of arity $p$:
--   $$
--   t:D^p\to D,\qquad t(a_1,a_2,\dots,a_p)=t(a_2,\dots,a_p,a_1).
--   $$
--
--   This is the relational form of the cyclic-term theorem of Barto and Kozik (2012); it supplies the operation used in the reconstruction argument.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: a finite constraint language Γ (a finite collection of relations R ⊆ D^r) → ConstraintLanguage: relations indexed by a finite type, duplicate names kept (p.10); singleton expansions Γ*, Γ_B add the pins as new indices; reason: Lean convention; duplicate relations change no polymorphism, endomorphism, solution set or complexity
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Theorem 2.2, p.12 (PDF 12), footnote 2

import Mathlib
import Definitions.Def_CSPIdealMem_Polymorphism

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Theorem 2.2 (cyclic polymorphisms; Barto–Kozik 2012, cited), p.12 (PDF 12).

If `Γ*` has a Taylor polymorphism then, for every prime `p > |D|`, `Γ*` has an idempotent cyclic
polymorphism of arity `p`.

**Formalization Note.** The domain is any nonempty finite type `α` (the statement does not use the
rational labels); `Γ* = Γ.withPins Finset.univ`. -/
theorem theorem_2_2 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (Γ : ConstraintLanguage α)
    (hT : HasTaylorPolymorphism (Γ.withPins Finset.univ)) (p : ℕ) (hp : p.Prime)
    (hpD : Fintype.card α < p) :
    ∃ t : (Fin p → α) → α,
      IsPolymorphism (Γ.withPins Finset.univ) t ∧ IsIdempotent t ∧ IsCyclic t := by sorry

end CSPIdealMem
