-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_A_5
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:22:19.324637+00:00
-- url     : https://prove2.me/theorems/bc6deeef-2b75-4afa-936c-cbfc9a3f89ee
-- title:
--   Lemma A.5 — Low-incidence total support
-- statement:
--   Let $n\ge1$, $1\le\ell\le n$, $K=\binom n\ell$, and let $H$ be a set of exactly $K$ distinct Boolean labelled views. Sample selected vertices independently and uniformly with replacement. Write $p=\ell/n$, $q=q_{\rm con}(H)$, and let $g$ choose any majority bit on every heavy coordinate $i$ with $z_i\ge p/8$, where $z_i$ is its incidence in the original $H$. Let $\varepsilon$ be the original-family fraction disagreeing with $g$ on at least one heavy coordinate, $L$ the strict low-incidence complement, and $\lambda=|L|/n$.
--
--   Under regime (20), $q<p/32$ and $\varepsilon\le16q/p<1/2$, one has
--
--   $$\ell\lambda\le9\varepsilon.$$
--
--   This bounds the total low-coordinate support and includes $L=\varnothing$ and $\varepsilon=0$.
--
--   Differences from the source:
--   - encoding: a set of K distinct Boolean labelled views → a Finset of published Vertex (Fin n coordinates) with card = choose n ell; reason: finite sets enforce distinctness and represent every source selection; normalization is unchanged
--   - encoding: a partial majority assignment on heavy coordinates → a total Boolean assignment constrained only on heavy coordinates; reason: every partial assignment extends; all extensions give the same survivor family and heavy error
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma A.5, PDF p20 / printed p19

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement

namespace BirthdayEntropy.Soundness.Supplement

/-- Lemma A.5, PDF p20 / printed p19. Includes empty L and zero error. -/
theorem lemma_A_5 (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (H : Finset (Vertex n ℓ)) (hH : H.card = Nat.choose n ℓ)
    (g : Fin n → Bool) (hg : IsMajority H g) (hsmall : SmallError H g) :
    (ℓ : ℝ) * lowFraction H ≤ 9 * heavyError H g := by sorry

end BirthdayEntropy.Soundness.Supplement
