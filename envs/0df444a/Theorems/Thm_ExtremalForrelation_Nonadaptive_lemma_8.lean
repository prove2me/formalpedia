-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_8
-- name    : ExtremalForrelation.Nonadaptive.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:23.295395+00:00
-- url     : https://prove2.me/theorems/4bd17ca7-3cfe-4d81-8e3e-040c8cb72e29
-- title:
--   Lemma 8 — the secret law $\mu_s(\cdot\mid K,\pi)$ and constrained anchor answers
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a subspace $K$ with $\dim K=m$, a query set $Q$, a bit $s$ and a bijection $\pi$, and consider $\mu_s(\cdot\mid K,\pi)$.
--
--   1. Every transcript in its support has the same pinning graph, which is determined by $K$ and $\pi$.
--   2. The anchor answers are uniform on the values that satisfy (10).
--   3. There are $2^{|F|+|G|-|E(\pi)|}$ such values, and each extends to exactly one transcript in the support.
--   4. Consequently, for every transcript $\tau$,
--   $$\mu_s(\tau\mid K,\pi)=2^{-|F|-|G|+|E(\pi)|}\,\mathbf 1_{(\pi,s)\bowtie\tau}. \tag{12}$$
--
--   Differences from the source:
--   - encoding: cosets C_1..C_M, D_1..D_M enumerated in a fixed way; π a uniform permutation of [M]; h : [M] → F_2 → cosets are the quotient types V⧸K and V⧸K^⊥; π a bijection V⧸K ≃ V⧸K^⊥; h a bit function on V⧸K; reason: transported along the fixed enumerations these are the same objects and the same uniform laws
--   - encoding: every transcript in the support has the same pinning graph, uniquely determined by K and π → for the fixed K, π there is a graph H with H_τ = H for every τ with μ_s(τ | K, π) > 0; reason: K and π are fixed in the statement, so existence of such H is the claim
--   - encoding: anchor answers uniform on the values satisfying (10) → the μ_s(· | K, π)-mass of the transcripts with anchor answers a is 2^{-|F|-|G|+|E(π)|} if a satisfies (10) and 0 otherwise; reason: this is the uniform law on the solutions of (10) given that there are 2^{|F|+|G|-|E(π)|} of them (natural-number subtraction is exact since |E(π)| ≤ |F|)
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 8, p. 14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 8 (p. 14). Fix `K`, `s` and `π`, and consider `μ_s(· | K, π)`. Every transcript in its
support has the same pinning graph; the anchor answers are uniform on the values satisfying (10),
there are `2^{|F|+|G|−|E(π)|}` such values and each extends to exactly one transcript in the
support; consequently `μ_s(τ | K, π) = 2^{−|F|−|G|+|E(π)|} 1_{(π,s) ⋈ τ}` (equation (12)). -/
theorem lemma_8 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (s : ZMod 2) (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) :
    (∃ H : V n ⧸ K → V n ⧸ orth K → Prop,
      ∀ τ : Transcript Q, 0 < muKP Q s K π τ → pinGraph Q K τ = H) ∧
    (∀ a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2),
      ∑ τ ∈ Finset.univ.filter (fun τ : Transcript Q => anchorAns Q K τ = a), muKP Q s K π τ =
        if Sat10 Q K π s a then
          (2 : ℝ) ^ (-((Fset Q K).card : ℤ) - (Gset Q K).card + (Eset Q K π).card)
        else 0) ∧
    ((Finset.univ.filter (fun a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2) =>
        Sat10 Q K π s a)).card = 2 ^ ((Fset Q K).card + (Gset Q K).card - (Eset Q K π).card)) ∧
    (∀ a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2), Sat10 Q K π s a →
      ∃! τ : Transcript Q, 0 < muKP Q s K π τ ∧ anchorAns Q K τ = a) ∧
    (∀ τ : Transcript Q, muKP Q s K π τ =
      (2 : ℝ) ^ (-((Fset Q K).card : ℤ) - (Gset Q K).card + (Eset Q K π).card) *
        (if CompatS Q K π s τ then 1 else 0)) := by sorry

end ExtremalForrelation.Nonadaptive
