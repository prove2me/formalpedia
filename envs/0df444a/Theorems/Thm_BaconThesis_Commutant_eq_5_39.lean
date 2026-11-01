-- Prove2me | Theorems.Thm_BaconThesis_Commutant_eq_5_39
-- name    : BaconThesis.Commutant.eq_5_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:38:10.731787+00:00
-- url     : https://prove2.me/theorems/7d59c301-7246-4c40-a6cb-1d458f0f3643
-- title:
--   (5.38)–(5.39) — the commutant of $\bigoplus_J I_{n_J}\otimes M_{d_J}$ is $\bigoplus_J M_{n_J}\otimes I_{d_J}$
-- statement:
--   Let $\mathcal J$ be a finite set of irrep labels with degeneracies $n_J\ge1$ and irrep dimensions $d_J\ge1$, let $W$ be a unitary from $\mathbb C^{\iota}$ onto $\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{d_J}$, and let
--   $$
--   A=\Bigl\{W^\dagger\Bigl(\bigoplus_J I_{n_J}\otimes X_J\Bigr)W : X_J\in M_{d_J}\Bigr\}\cong\bigoplus_{J\in\mathcal J} I_{n_J}\otimes M_{d_J}.
--   $$
--   Then the commutant $A'=\{T : Ta=aT \text{ for all } a\in A\}$ is
--   $$
--   A'=\Bigl\{W^\dagger\Bigl(\bigoplus_J Y_J\otimes I_{d_J}\Bigr)W : Y_J\in M_{n_J}\Bigr\}\cong\bigoplus_{J\in\mathcal J} M_{n_J}\otimes I_{d_J}.
--   $$
--   Both inclusions are asserted.
--
--   This is the dual block structure behind the commutant condition of Chapter 7: operators commuting with the OSR algebra act only on the degeneracies, where decoherence-free information is stored.
--
--   **Formalization Note** The commutant is Mathlib's `Set.centralizer`; unitarity of $W$ is $W^\dagger W=1$ and $WW^\dagger=1$.
--
--   Differences from the source:
--   - encoding: A ≅ ⊕_J I_{n_J} ⊗ M_{d_J} ("there is a basis such that") → A = {W† (⊕_J I_{n_J} ⊗ X_J) W} for an explicit unitary W; reason: the orthonormal basis change of Theorem 5.4.1 made explicit; same instances
--   - encoding: irreps J ∈ 𝒥 of Theorem 5.4.1 (each irrep present, with a degeneracy n_J and a dimension d_J) → hypotheses ∀ J, 0 < n J and ∀ J, 0 < d J; reason: the book's irreps and degeneracies are nonzero; an empty block would contribute nothing to any operator, so no instance changes
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.3, eqs. (5.38)–(5.39), p.80 (PDF p.97); restated as eq. (7.2), p.100 (PDF p.117)

import Mathlib
import Definitions.Def_BaconThesis_Commutant_blockC
import Definitions.Def_BaconThesis_Commutant_algebraA

namespace BaconThesis.Commutant

/-- **The commutant of `⊕_J I_{n_J} ⊗ M_{d_J}` is `⊕_J M_{n_J} ⊗ I_{d_J}`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.3, eqs. (5.38)–(5.39), p.80 (PDF p.97): "If the algebra `A` is reducible to the form
`A ≅ ⊕_{J∈𝒥} I_{n_J} ⊗ M_{d_J}`, (5.38) as in Eq. (5.30), then the commutant of the algebra is
reducible to the form `A′ ≅ ⊕_{J∈𝒥} M_{n_J} ⊗ I_{d_J}`. (5.39)" (restated as (7.2), p.100).

Let `𝒥` be a finite set of irrep labels with degeneracies `n_J ≥ 1` and irrep dimensions
`d_J ≥ 1`, let `W` be a unitary from `ℂ^ι` onto `⊕_J ℂ^{n_J} ⊗ ℂ^{d_J}`, and let
`A = {W† (⊕_J I_{n_J} ⊗ X_J) W : X_J ∈ M_{d_J}}`. Then the commutant `A′` (the set of operators
`T` with `aT = Ta` for every `a ∈ A`) is exactly `{W† (⊕_J Y_J ⊗ I_{d_J}) W : Y_J ∈ M_{n_J}}`.

**Formalization Note.** The commutant is Mathlib's `Set.centralizer`. Both inclusions are asserted
(set equality). Unitarity of `W` is `W† W = 1` and `W W† = 1`. -/
theorem eq_5_39 {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1) :
    Set.centralizer (algebraA n d W) =
      {T | ∃ Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ,
        T = W.conjTranspose * blockC n d Y * W} := by sorry

end BaconThesis.Commutant
