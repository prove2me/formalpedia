-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_7
-- name    : ExtremalForrelation.Nonadaptive.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:32.369387+00:00
-- url     : https://prove2.me/theorems/866bdea7-28cf-4c01-acb4-8f19ee51fa74
-- title:
--   Lemma 7 — the reference law $\rho(\cdot\mid K,\pi)$ and uniform anchor answers
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a subspace $K$ with $\dim K=m$, a query set $Q$ and a bijection $\pi$, and consider $\rho(\cdot\mid K,\pi)$.
--
--   1. Every transcript in its support has the same pinning graph, which is determined by $K$ and $\pi$.
--   2. The anchor answers are uniform on $\mathbb F_2^{|F|+|G|}$.
--   3. Each of their $2^{|F|+|G|}$ values extends to exactly one transcript in the support.
--   4. Consequently, for every transcript $\tau$,
--   $$\rho(\tau\mid K,\pi)=2^{-|F|-|G|}\,\mathbf 1_{\pi\bowtie\tau}. \tag{11}$$
--
--   Differences from the source:
--   - encoding: cosets C_1..C_M, D_1..D_M enumerated in a fixed way; π a uniform permutation of [M]; h : [M] → F_2 → cosets are the quotient types V⧸K and V⧸K^⊥; π a bijection V⧸K ≃ V⧸K^⊥; h a bit function on V⧸K; reason: transported along the fixed enumerations these are the same objects and the same uniform laws
--   - encoding: every transcript in the support has the same pinning graph, uniquely determined by K and π → for the fixed K, π there is a graph H with H_τ = H for every τ with ρ(τ | K, π) > 0; reason: K and π are fixed in the statement, so existence of such H is the claim
--   - encoding: anchor answers uniform on F_2^{|F|+|G|} → for every anchor-answer vector a, the ρ(· | K, π)-mass of the transcripts with anchor answers a is 2^{-|F|-|G|}; reason: this is the law of the anchor answers; anchors are the smallest queries in each queried coset, a choice depending only on Q and K
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 7, p. 14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 7 (p. 14). Fix `K` and `π`, and consider `ρ(· | K, π)`. Every transcript in its support
has the same pinning graph; the anchor answers are uniform on `𝔽₂^{|F|+|G|}`, and each of their
values extends to exactly one transcript in the support; consequently
`ρ(τ | K, π) = 2^{−|F|−|G|} 1_{π ⋈ τ}` for every `τ` (equation (11)). -/
theorem lemma_7 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) :
    (∃ H : V n ⧸ K → V n ⧸ orth K → Prop,
      ∀ τ : Transcript Q, 0 < rhoKP Q K π τ → pinGraph Q K τ = H) ∧
    (∀ a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2),
      ∑ τ ∈ Finset.univ.filter (fun τ : Transcript Q => anchorAns Q K τ = a), rhoKP Q K π τ =
        (2 : ℝ) ^ (-(((Fset Q K).card + (Gset Q K).card : ℕ) : ℤ))) ∧
    (∀ a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2),
      ∃! τ : Transcript Q, 0 < rhoKP Q K π τ ∧ anchorAns Q K τ = a) ∧
    (∀ τ : Transcript Q, rhoKP Q K π τ =
      (2 : ℝ) ^ (-(((Fset Q K).card + (Gset Q K).card : ℕ) : ℤ)) *
        (if Compat Q K π τ then 1 else 0)) := by sorry

end ExtremalForrelation.Nonadaptive
