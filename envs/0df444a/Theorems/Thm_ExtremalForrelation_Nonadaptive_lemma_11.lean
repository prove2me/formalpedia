-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_11
-- name    : ExtremalForrelation.Nonadaptive.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:48.439997+00:00
-- url     : https://prove2.me/theorems/dbb8f7e3-4809-430b-9b66-e681d4121f0c
-- title:
--   Lemma 11 — sum of squared matching probabilities
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a query set $Q$ with $q=|Q|$, a subspace $K$ with $\dim K=m$ that is $r$-good for $Q$ (for an integer $r\ge1$), and a transcript $\tau$ with $\rho(\tau\mid K)>0$; let $H=H_\tau$ be its pinning graph.
--   Suppose further that $q\le M/2^{r+3}$ and that
--   $$\beta=|F|\,|G|\Big(\frac{4^{r+1}}{M}\Big)^2<1 .$$
--   Then
--   $$\sum_{\substack{I\subseteq F,\ J\subseteq G\\ |I|=|J|\ge1}}p_{I,J}(H)^2\le\frac{\beta}{1-\beta}.$$
--
--   Combined with Lemma 9 this gives $\|\mu_s(\cdot\mid K)-\rho(\cdot\mid K)\|_{TV}\le4^{r+1}q/M$ in the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: 'for K, H and τ as above' (K r-good, H the pinning graph of τ with ρ(τ | K) > 0) → hypotheses IsGood Q r K with 1 ≤ r, 0 < ρ(τ | K), and H written as pinGraph Q K τ; reason: the inherited setting of Lemma 10, stated explicitly
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 11, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 11 (p. 19). Let `K` be `r`-good and `H` the pinning graph of a transcript `τ` with
`ρ(τ | K) > 0`. Suppose `q ≤ M/2^{r+3}` and `β = |F| |G| (4^{r+1}/M)² < 1`. Then
`∑_{I ⊆ F, J ⊆ G, |I| = |J| ≥ 1} p_{I,J}(H)² ≤ β/(1 − β)`. -/
theorem lemma_11 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (r : ℕ) (hr : 1 ≤ r) (hgood : IsGood Q r K)
    (τ : Transcript Q) (hτ : 0 < rhoK Q K τ)
    (hq : (Q.card : ℝ) ≤ (2 : ℝ) ^ (n / 2) / 2 ^ (r + 3))
    (hβ : ((Fset Q K).card : ℝ) * (Gset Q K).card * ((4 : ℝ) ^ (r + 1) / 2 ^ (n / 2)) ^ 2 < 1) :
    sumSqMatchProb Q K (pinGraph Q K τ) ≤
      ((Fset Q K).card : ℝ) * (Gset Q K).card * ((4 : ℝ) ^ (r + 1) / 2 ^ (n / 2)) ^ 2 /
        (1 - ((Fset Q K).card : ℝ) * (Gset Q K).card * ((4 : ℝ) ^ (r + 1) / 2 ^ (n / 2)) ^ 2) := by sorry

end ExtremalForrelation.Nonadaptive
