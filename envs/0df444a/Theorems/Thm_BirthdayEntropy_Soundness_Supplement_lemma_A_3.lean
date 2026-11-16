-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_A_3
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:38.896487+00:00
-- url     : https://prove2.me/theorems/fcdb2db1-2e9a-4370-9cbd-edc9517eb1f8
-- title:
--   Lemma A.3 — Hypergeometric moments and KL comparison
-- statement:
--   Let $n\ge1$, $1\le\ell\le n$, $L\subseteq[n]$, $\lambda=|L|/n$, $u$ the uniform law on all $\ell$-views, and $\mu$ any probability law on them, allowing zero atoms. Put $x=\mathbb E_\mu|S\cap L|/\ell$. For every real $t$,
--
--   $$\mathbb E_u e^{t|S\cap L|}\le(1-\lambda+\lambda e^t)^\ell.$$
--
--   If $0<\lambda<1$, also
--
--   $$D_{\rm KL}(\mu\|u)\ge\ell d(x\|\lambda),\qquad d(x\|\lambda)=x\log(x/\lambda)+(1-x)\log((1-x)/(1-\lambda)).$$
--
--   The binary divergence uses the continuous convention at $x=0,1$. The moment bound includes $\lambda=0,1$ and negative tilts; only the KL conclusion restricts $\lambda$. This compares arbitrary view bias with its information cost. The shared moment clause has the existing Open proof dependency RandOrderSort.lemma_4_5; that partial result does not supply the arbitrary-law KL clause.
--
--   Differences from the source:
--   - encoding: arbitrary view law and KL against uniform all-view law → published finite Law and real relativeEntropy, with published Bernoulli divergence; reason: uniform reference masses are positive; zero numerator terms vanish and endpoints have the continuous values
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma A.3, PDF p19-20 / printed p18-19

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement
import Definitions.Def_bernoulliRelativeEntropy

namespace BirthdayEntropy.Soundness.Supplement
open OAI.ThorpCompatibility

/-- Lemma A.3, (24)–(25), PDF pp19–20 / printed pp18–19. Arbitrary L
and arbitrary view law; every real tilt, including negative ones and endpoint incidences. -/
theorem lemma_A_3 (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (L : Finset (Fin n)) (μ : Law (View n ℓ)) :
    let lam := (L.card : ℝ) / n
    let x := lowIncidence μ L
    let u := allViewLaw n ℓ hℓn
    (∀ t : ℝ, u.mean (fun S => Real.exp (t * ((S.val ∩ L).card : ℝ))) ≤
      (1 - lam + lam * Real.exp t)^ℓ) ∧
    (0 < lam → lam < 1 →
      (ℓ : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy x lam ≤ μ.relativeEntropy u) := by sorry

end BirthdayEntropy.Soundness.Supplement
