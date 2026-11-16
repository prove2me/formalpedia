-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_A_2
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:37.823862+00:00
-- url     : https://prove2.me/theorems/a68d8bcd-8dfe-475b-a002-f8d00bb9814e
-- title:
--   Lemma A.2 — Incidence and conditional-entropy budget
-- statement:
--   Let $n\ge1$, $1\le\ell\le n$, $K=\binom n\ell$, and let $H$ be a set of exactly $K$ distinct Boolean labelled views. Sample selected vertices independently and uniformly with replacement. Write $p=\ell/n$, $q=q_{\rm con}(H)$, and let $g$ choose any majority bit on every heavy coordinate $i$ with $z_i\ge p/8$, where $z_i$ is its incidence in the original $H$. Let $\varepsilon$ be the original-family fraction disagreeing with $g$ on at least one heavy coordinate, $L$ the strict low-incidence complement, and $\lambda=|L|/n$.
--
--   Assume regime (20): $q<p/32$ and $\varepsilon\le16q/p<1/2$. Let $G$ be the actual surviving subfamily agreeing with $g$ on heavy coordinates. Then $G$ is nonempty, $m=|G|=(1-\varepsilon)K$. Sample $(S,A)$ uniformly from $G$, let $\mu$ be its view marginal and $u$ uniform on all views, and put $x=\mathbb E_\mu|S\cap L|/\ell$. All three conclusions hold:
--
--   $$0\le x\le\frac{\lambda}{8(1-\varepsilon)}\le\frac\lambda4,$$
--   $$H(A\mid S)\le\ell x\log2,$$
--   $$D_{\rm KL}(\mu\|u)=\log(K/m)+H(A\mid S)\le-\log(1-\varepsilon)+\ell x\log2.$$
--
--   This exact identity retains the conditional answer entropy and accounts for missing views and distinctness of the surviving labelled pairs.
--
--   Differences from the source:
--   - encoding: a set of K distinct Boolean labelled views → a Finset of published Vertex (Fin n coordinates) with card = choose n ell; reason: finite sets enforce distinctness and represent every source selection; normalization is unchanged
--   - encoding: a partial majority assignment on heavy coordinates → a total Boolean assignment constrained only on heavy coordinates; reason: every partial assignment extends; all extensions give the same survivor family and heavy error
--   - encoding: uniform survivor law after (20) establishes m>0 → existence of a nonempty-survivor certificate followed by the bounds; signed labels encode A given S; reason: no positivity assumption is added; within a view the signed representation is injective
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma A.2, PDF p19 / printed p18

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement

namespace BirthdayEntropy.Soundness.Supplement

/-- Lemma A.2, (21)–(23), PDF p19 / printed p18. Nonemptiness of G is
concluded, not assumed. The signed representation preserves A conditional on S. -/
theorem lemma_A_2 (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (H : Finset (Vertex n ℓ)) (hH : H.card = Nat.choose n ℓ)
    (g : Fin n → Bool) (hg : IsMajority H g) (hsmall : SmallError H g) :
    ∃ hG : (survivors H g).Nonempty,
      let ε := heavyError H g
      let lam := lowFraction H
      let μ := survivorViews H g hG
      let x := lowIncidence μ (low H)
      let ha := answerEntropy H g hG
      let kl := μ.relativeEntropy (allViewLaw n ℓ hℓn)
      ((survivors H g).card : ℝ) = (1 - ε) * Nat.choose n ℓ ∧
      (0 ≤ x ∧ x ≤ lam / (8 * (1 - ε)) ∧ lam / (8 * (1 - ε)) ≤ lam / 4) ∧
      ha ≤ (ℓ : ℝ) * x * Real.log 2 ∧
      kl = Real.log ((Nat.choose n ℓ : ℝ) / (survivors H g).card) + ha ∧
      kl ≤ -Real.log (1 - ε) + (ℓ : ℝ) * x * Real.log 2 := by sorry

end BirthdayEntropy.Soundness.Supplement
