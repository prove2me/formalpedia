-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_claim_2
-- name    : ExtremalForrelation.Nonadaptive.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:39.525447+00:00
-- url     : https://prove2.me/theorems/24639844-514f-4d36-9dc1-aa500e1fd6f9
-- title:
--   Claim 2 — adding an edge shrinks the set of extending matchings
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a query set $Q$ with $q=|Q|$, a subspace $K$ with $\dim K=m$ that is $r$-good for $Q$ (for an integer $r\ge1$), and a transcript $\tau$ with $\rho(\tau\mid K)>0$; let $H=H_\tau$ be its pinning graph.
--   Assume $1\le q\le M/2^{r+3}$. Fix any partial matching $T\subseteq F\times G$ and any edge $(i_1,j_1)\in(F\times G)\setminus T$. Then
--   $$\big|\Pi_{T\cup\{(i_1,j_1)\}}\big|\le\frac{4^{r+1}}{M}\,|\Pi_T|, \tag{20}$$
--   where $\Pi_T$ is the set of perfect matchings of $H$ containing every edge of $T$.
--
--   Iterating this edge by edge gives Lemma 10.
--
--   Differences from the source:
--   - encoding: 'for K, H and τ as above' (K r-good, H the pinning graph of τ with ρ(τ | K) > 0) → hypotheses IsGood Q r K with 1 ≤ r, 0 < ρ(τ | K), and H written as pinGraph Q K τ; reason: the inherited setting of Lemma 10, stated explicitly
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Claim 2 (in the proof of Lemma 10), p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Claim 2 (p. 18), in the setting of Lemma 10. Assume `1 ≤ q ≤ M/2^{r+3}`. For any partial
matching `T ⊆ F × G` and any edge `(i₁, j₁) ∈ (F × G) \ T`,
`|Π_{T ∪ {(i₁, j₁)}}| ≤ (4^{r+1}/M) |Π_T|` (equation (20)), where `Π_T` is the set of perfect
matchings of `H = H_τ` containing every edge of `T`. -/
theorem claim_2 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (r : ℕ) (hr : 1 ≤ r) (hgood : IsGood Q r K)
    (τ : Transcript Q) (hτ : 0 < rhoK Q K τ)
    (hq1 : 1 ≤ Q.card) (hq : (Q.card : ℝ) ≤ (2 : ℝ) ^ (n / 2) / 2 ^ (r + 3))
    (T : Finset ((V n ⧸ K) × (V n ⧸ orth K))) (hT : T ⊆ Fset Q K ×ˢ Gset Q K)
    (hTm : IsPartialMatching T) (e : (V n ⧸ K) × (V n ⧸ orth K))
    (he : e ∈ (Fset Q K ×ˢ Gset Q K) \ T) :
    ((PiT (pinGraph Q K τ) (insert e T)).card : ℝ) ≤
      (4 : ℝ) ^ (r + 1) / 2 ^ (n / 2) * (PiT (pinGraph Q K τ) T).card := by sorry

end ExtremalForrelation.Nonadaptive
