-- Prove2me | Theorems.Thm_CircTrichotomy_lemma_B_13
-- name    : CircTrichotomy.lemma_B_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:13.644895+00:00
-- url     : https://prove2.me/theorems/330beda5-1bef-4434-acbe-a41cf65d5563
-- title:
--   Lemma B.13 — the exchange principle
-- statement:
--   **Lemma B.13** (Exchange Principle). Let $\varphi:\Sigma^+\to S$ be a stamp in $\mathbf X$ with stability index $s$. Let $u,v,w$ be non-empty words whose lengths are multiples of $s$, with $\varphi(u)$ and $\varphi(w)$ idempotent. Then for all positions $i<|u|$, $j<|v|$, $k<|w|$ with $i\equiv_s j\equiv_s k$,
--   $$\varphi\bigl(u\,v[j\leftarrow u_i]\,w\bigr)=\varphi\bigl(u\,v[j\leftarrow w_k]\,w\bigr).$$
--
--   A letter between two idempotent blocks can be exchanged for a letter of the same residue class taken from either block.
--
--   Differences from the source:
--   - encoding: a stamp φ : Σ⁺ → S → a MulHom φ : FreeSemigroup α →ₙ* S with IsStamp φ (surjective, S finite); reason: FreeSemigroup α is Σ⁺ with concatenation
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
--   - reading: φ : Σ⁺ → S a morphism in X with stability index s → IsStamp φ (surjective onto a finite S) and InX φ; reason: X is a class of stamps (Definition 2.3) and the stability index is defined for morphisms onto a finite semigroup (p.3, p.17)
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma B.13, p.26

import Mathlib
import Definitions.Def_CircTrichotomy_wordToList
import Definitions.Def_CircTrichotomy_IsStamp
import Definitions.Def_CircTrichotomy_IsStabilityIndex
import Definitions.Def_CircTrichotomy_InX

set_option autoImplicit false

namespace CircTrichotomy

/-- **Lemma B.13 (Exchange Principle)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Lemma B.13, p.26): "Let φ : Σ⁺ → S be a morphism in X
with stability index s ∈ ℕ>0. Let u, v, w ∈ Σ^{sℕ>0} be words and in particular let u and w be
idempotents. Assume that u = u₀ … u_{|u|−1}, v = v₀ … v_{|v|−1} and w = w₀ … w_{|w|−1}. Then for all
i ∈ [0, |u| − 1], j ∈ [0, |v| − 1], k ∈ [0, |w| − 1] such that i ≡_s j ≡_s k, we have
uv[j ← u_i]w =_φ uv[j ← w_k]w.   (49)"

**Formalization Note** "A morphism in X with stability index s" is a stamp (`IsStamp`; X is a class
of stamps, and the stability index is defined for morphisms onto a finite semigroup, p.3).
`Σ^{sℕ>0}` is the set of non-empty words whose length is a multiple of `s` (p.16). -/
theorem lemma_B_13 {α S : Type} [Fintype α] [Nonempty α] [Semigroup S]
    (φ : FreeSemigroup α →ₙ* S) (hφ : IsStamp φ) (hX : InX φ) (s : ℕ)
    (hs : IsStabilityIndex φ s) (u v w : FreeSemigroup α) (hu : s ∣ u.length)
    (hv : s ∣ v.length) (hw : s ∣ w.length) (hu_idem : φ u * φ u = φ u)
    (hw_idem : φ w * φ w = φ w) (i j k : ℕ) (hi : i < u.length) (hj : j < v.length)
    (hk : k < w.length) (hij : i % s = j % s) (hjk : j % s = k % s) :
    φ (u * setAt v j (letterAt u i) * w) = φ (u * setAt v j (letterAt w k) * w) := by sorry

end CircTrichotomy
