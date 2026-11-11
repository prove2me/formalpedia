-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_5_5
-- name    : CSPIdealMem.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:58.097995+00:00
-- url     : https://prove2.me/theorems/f0f32ed0-d6f2-4677-9d93-a2d108444783
-- title:
--   Lemma 5.5 — a minimal principal left ideal permits a return to $e$
-- statement:
--   Let $M=\mathrm{End}(\Gamma)$ and let $F:M\to\mathbb Q$ be nonzero somewhere. Choose $e\in M$ with $F(e)\neq0$ minimizing $|Me|$ among such maps. Then for every $h\in M$ with $F(h\circ e)\neq0$ there is $k\in M$ with
--   $$
--   k\circ h\circ e=e,
--   $$
--   and consequently $k\circ h$ fixes $e(D)$ pointwise.
--
--   It is what lets the reduction restore the pinned values.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: F : M → Q, nonzero somewhere → F a function on all maps D → D; "nonzero somewhere" is not stated separately; reason: only values on endomorphisms enter, and F(e) ≠ 0 for the chosen e already gives it
--   - encoding: a finite constraint language Γ (a finite collection of relations R ⊆ D^r) → ConstraintLanguage: relations indexed by a finite type, duplicate names kept (p.10); singleton expansions Γ*, Γ_B add the pins as new indices; reason: Lean convention; duplicate relations change no polymorphism, endomorphism, solution set or complexity
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 5.5, p.35 (PDF 35); Me, p.35

import Mathlib
import Definitions.Def_CSPIdealMem_Polymorphism

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 5.5, p.35 (PDF 35); `Me`, p.35.

Let `F : M → ℚ` (`M = End(Γ)`) be nonzero somewhere, and choose `e ∈ M` with `F(e) ≠ 0` minimizing
`|Me|`. For every `h ∈ M` with `F(h ∘ e) ≠ 0` there is `k ∈ M` with `k ∘ h ∘ e = e`; consequently
`k ∘ h` fixes `e(D)` pointwise.

**Formalization Note.** `F` is a function on all maps `α → α`; only its values on endomorphisms
enter. "Nonzero somewhere" is implied by `F(e) ≠ 0` and is not repeated. The domain is any
nonempty finite type `α`. -/
theorem lemma_5_5 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (Γ : ConstraintLanguage α) (F : (α → α) → ℚ)
    (e : α → α) (he : IsEndomorphism Γ e) (hFe : F e ≠ 0)
    (hmin : ∀ e' : α → α, IsEndomorphism Γ e' → F e' ≠ 0 →
      (leftIdeal Γ e).ncard ≤ (leftIdeal Γ e').ncard)
    (h : α → α) (hh : IsEndomorphism Γ h) (hFh : F (h ∘ e) ≠ 0) :
    ∃ k : α → α, IsEndomorphism Γ k ∧ k ∘ h ∘ e = e ∧ ∀ b ∈ Set.range e, k (h b) = b := by sorry

end CSPIdealMem
