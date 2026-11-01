-- Prove2me | Theorems.Thm_BaconThesis_Commutant_double_commutant
-- name    : BaconThesis.Commutant.double_commutant
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:38:19.092016+00:00
-- url     : https://prove2.me/theorems/aec0d891-7a92-41e7-85e4-e3efd6568462
-- title:
--   §5.4.3 — the double commutant of $\bigoplus_J I_{n_J}\otimes M_{d_J}$ is the algebra itself
-- statement:
--   Let $\mathcal J$ be a finite set of irrep labels with degeneracies $n_J\ge1$ and irrep dimensions $d_J\ge1$, let $W$ be a unitary from $\mathbb C^{\iota}$ onto $\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{d_J}$, and let
--   $$
--   A=\Bigl\{W^\dagger\Bigl(\bigoplus_J I_{n_J}\otimes X_J\Bigr)W : X_J\in M_{d_J}\Bigr\}.
--   $$
--   Then the commutant of the commutant of $A$ is $A$:
--   $$
--   (A')'=A .
--   $$
--
--   Together with (5.39) this says that $A$ and $A'$ determine each other: an algebra of the form (5.38) is recovered from its commutant.
--
--   **Formalization Note** The commutant is Mathlib's `Set.centralizer`.
--
--   Differences from the source:
--   - reading: "the commutant of the commutant of an algebra is itself the algebra" (said of the OSR algebra, a †-closed algebra containing the identity) → A in the decomposed form (5.38); reason: by the cited Theorem 5.4.1 every †-closed algebra containing the identity has this form, and the sentence is not true of arbitrary algebras (the upper-triangular 2 × 2 matrices have commutant ℂI and double commutant M₂)
--   - encoding: A ≅ ⊕_J I_{n_J} ⊗ M_{d_J} → A = {W† (⊕_J I_{n_J} ⊗ X_J) W} for an explicit unitary W; reason: the basis change of Theorem 5.4.1 made explicit; same instances
--   - encoding: irreps J ∈ 𝒥 of Theorem 5.4.1 (each irrep present, with a degeneracy n_J and a dimension d_J) → hypotheses ∀ J, 0 < n J and ∀ J, 0 < d J; reason: the book's irreps and degeneracies are nonzero; an empty block would contribute nothing to any operator, so no instance changes
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.3, p.80 (PDF p.97)

import Mathlib
import Definitions.Def_BaconThesis_Commutant_algebraA

namespace BaconThesis.Commutant

/-- **The double commutant of `⊕_J I_{n_J} ⊗ M_{d_J}` is the algebra itself.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.3, p.80 (PDF p.97): "The commutant of the commutant of an algebra is itself the algebra
`(A′)′ = A`", stated there for the algebras of the form (5.38).

Let `𝒥` be a finite set of irrep labels with degeneracies `n_J ≥ 1` and irrep dimensions
`d_J ≥ 1`, let `W` be a unitary from `ℂ^ι` onto `⊕_J ℂ^{n_J} ⊗ ℂ^{d_J}`, and let
`A = {W† (⊕_J I_{n_J} ⊗ X_J) W : X_J ∈ M_{d_J}}`. Then `(A′)′ = A`.

**Formalization Note.** The commutant is Mathlib's `Set.centralizer`. The book states the double
commutant property for the OSR algebra, a †-closed algebra containing the identity, which
Theorem 5.4.1 (cited) puts in the form (5.38); that form is the hypothesis here. -/
theorem double_commutant {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1) :
    Set.centralizer (Set.centralizer (algebraA n d W)) = algebraA n d W := by sorry

end BaconThesis.Commutant
