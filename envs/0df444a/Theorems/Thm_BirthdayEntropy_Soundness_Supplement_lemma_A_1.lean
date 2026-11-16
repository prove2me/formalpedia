-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_A_1
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:19:56.092284+00:00
-- url     : https://prove2.me/theorems/6aa80d81-0374-4db7-afd6-fdc7085e0a7f
-- title:
--   Lemma A.1 — Heavy-coordinate majority decoding
-- statement:
--   Let $n\ge1$, $1\le\ell\le n$, $K=\binom n\ell$, and let $H$ be a set of exactly $K$ distinct Boolean labelled views. Sample selected vertices independently and uniformly with replacement. Write $p=\ell/n$, $q=q_{\rm con}(H)$, and let $g$ choose any majority bit on every heavy coordinate $i$ with $z_i\ge p/8$, where $z_i$ is its incidence in the original $H$. Let $\varepsilon$ be the original-family fraction disagreeing with $g$ on at least one heavy coordinate, $L$ the strict low-incidence complement, and $\lambda=|L|/n$.
--
--   Then
--
--   $$\varepsilon\le\frac{16q}{p}.$$
--
--   The bound permits every majority tie-breaking choice and supplies the heavy-coordinate error estimate for agreement stability.
--
--   Differences from the source:
--   - encoding: a set of K distinct Boolean labelled views → a Finset of published Vertex (Fin n coordinates) with card = choose n ell; reason: finite sets enforce distinctness and represent every source selection; normalization is unchanged
--   - encoding: a partial majority assignment on heavy coordinates → a total Boolean assignment constrained only on heavy coordinates; reason: every partial assignment extends; all extensions give the same survivor family and heavy error
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma A.1, PDF p18 / printed p17

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement

namespace BirthdayEntropy.Soundness.Supplement

/-- Lemma A.1, PDF p18 / printed p17. Any heavy-coordinate majority choice. -/
theorem lemma_A_1 (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (H : Finset (Vertex n ℓ)) (hH : H.card = Nat.choose n ℓ)
    (g : Fin n → Bool) (hg : IsMajority H g) :
    heavyError H g ≤ 16 * qcon H / ratio n ℓ := by sorry

end BirthdayEntropy.Soundness.Supplement
