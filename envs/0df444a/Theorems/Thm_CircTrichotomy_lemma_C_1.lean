-- Prove2me | Theorems.Thm_CircTrichotomy_lemma_C_1
-- name    : CircTrichotomy.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:00.232286+00:00
-- url     : https://prove2.me/theorems/1ccb142f-659c-4071-9cf2-37f2b8f2e3e5
-- title:
--   Lemma C.1 — a witness of non-membership in $\mathbf X$
-- statement:
--   **Lemma C.1.** Let $\varphi:\Sigma^+\to S$ be a stamp that is not in $\mathbf X$, with stability index $s$. Then there are $k\ge1$ with $s\mid k$, words $u,v,w\in\Sigma^k$ with $\varphi(u)$ and $\varphi(w)$ idempotent, and a position $i\in[0,k-1]$ such that
--   $$\varphi\bigl(u\,v[i\leftarrow(u)_i]\,w\bigr)\ne\varphi\bigl(u\,v[i\leftarrow(w)_i]\,w\bigr).$$
--
--   A single-letter exchange thus distinguishes two words under $\varphi$; this is the input of the linear lower bound.
--
--   Differences from the source:
--   - encoding: a stamp φ : Σ⁺ → S → a MulHom φ : FreeSemigroup α →ₙ* S with IsStamp φ (surjective, S finite); reason: FreeSemigroup α is Σ⁺ with concatenation
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
--   - encoding: k is a multiple of the stability index of φ → ∃ s, IsStabilityIndex φ s ∧ ∃ k, 0 < k ∧ s ∣ k ∧ …; reason: the stability index of a stamp exists and is unique, so this is the source's statement; k ≥ 1 because u ∈ Σᵏ is non-empty
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma C.1, p.43

import Mathlib
import Definitions.Def_CircTrichotomy_wordToList
import Definitions.Def_CircTrichotomy_IsStamp
import Definitions.Def_CircTrichotomy_IsStabilityIndex
import Definitions.Def_CircTrichotomy_InX

set_option autoImplicit false

namespace CircTrichotomy

/-- **Lemma C.1 (X non-membership witness)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma C.1, p.43): "If a stamp φ : Σ⁺ → S is not
in X, then uv[i ← (u)_i]w ≠_φ uv[i ← (w)_i]w for some u, v, w ∈ Σᵏ, where k is a multiple of the
stability index of φ, i ∈ [0, k − 1] and u and w are idempotents."

For a stamp `φ` not in `X`: with `s` the stability index of `φ`, there are `k ≥ 1` with `s ∣ k`, words
`u, v, w` of length `k` with `φ(u)`, `φ(w)` idempotent, and `i < k` such that
`φ(u · v[i ← (u)_i] · w) ≠ φ(u · v[i ← (w)_i] · w)`.

**Formalization Note** The conclusion also asserts that the stability index exists (it does for
every stamp). "u is an idempotent" means `φ(u)` is idempotent (p.16). -/
theorem lemma_C_1 {α S : Type} [Fintype α] [Nonempty α] [Semigroup S]
    (φ : FreeSemigroup α →ₙ* S) (hφ : IsStamp φ) (hX : ¬ InX φ) :
    ∃ s : ℕ, IsStabilityIndex φ s ∧ ∃ k : ℕ, 0 < k ∧ s ∣ k ∧
      ∃ u v w : FreeSemigroup α, u.length = k ∧ v.length = k ∧ w.length = k ∧
        φ u * φ u = φ u ∧ φ w * φ w = φ w ∧
        ∃ i < k, φ (u * setAt v i (letterAt u i) * w) ≠ φ (u * setAt v i (letterAt w i) * w) := by sorry

end CircTrichotomy
