-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_10
-- name    : ExtremalForrelation.Nonadaptive.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:30.311519+00:00
-- url     : https://prove2.me/theorems/09f0e347-2d23-4ac2-b383-9b7d5a9b49ae
-- title:
--   Lemma 10 — a random perfect matching rarely contains a given matching
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a query set $Q$ with $q=|Q|$, a subspace $K$ with $\dim K=m$ that is $r$-good for $Q$ (for an integer $r\ge1$), and a transcript $\tau$ with $\rho(\tau\mid K)>0$; let $H=H_\tau$ be its pinning graph.
--   Suppose further that $q\le M/2^{r+3}$. Then for every matching $T\subseteq F\times G$,
--   $$\Pr_{\pi\bowtie H}\big[T\subseteq E(\pi)\big]\le\Big(\frac{4^{r+1}}{M}\Big)^{|T|},$$
--   where $\pi$ is uniform among the perfect matchings of $H$.
--
--   Differences from the source:
--   - encoding: 'for K, H and τ as above' (K r-good, H the pinning graph of τ with ρ(τ | K) > 0) → hypotheses IsGood Q r K with 1 ≤ r, 0 < ρ(τ | K), and H written as pinGraph Q K τ; reason: the inherited setting of Lemma 10, stated explicitly
--   - encoding: a matching T ⊆ F × G → a finite set T ⊆ F × G of edges no two of which share an endpoint (IsPartialMatching); reason: the paper's matchings are partial matchings; the empty matching is allowed
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 10, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 10 (p. 17). Let `K` be `r`-good and `H` the pinning graph of a transcript `τ` with
`ρ(τ | K) > 0`, and suppose `q ≤ M/2^{r+3}`. Then for every matching `T ⊆ F × G`,
`Pr_{π ⋈ H}[T ⊆ E(π)] ≤ (4^{r+1}/M)^{|T|}`, for `π` uniform among the perfect matchings of `H`. -/
theorem lemma_10 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (r : ℕ) (hr : 1 ≤ r) (hgood : IsGood Q r K)
    (τ : Transcript Q) (hτ : 0 < rhoK Q K τ)
    (hq : (Q.card : ℝ) ≤ (2 : ℝ) ^ (n / 2) / 2 ^ (r + 3))
    (T : Finset ((V n ⧸ K) × (V n ⧸ orth K))) (hT : T ⊆ Fset Q K ×ˢ Gset Q K)
    (hTm : IsPartialMatching T) :
    (((PMs (pinGraph Q K τ)).filter (fun π => T ⊆ Eset Q K π)).card : ℝ) /
        (PMs (pinGraph Q K τ)).card ≤
      ((4 : ℝ) ^ (r + 1) / 2 ^ (n / 2)) ^ T.card := by sorry

end ExtremalForrelation.Nonadaptive
