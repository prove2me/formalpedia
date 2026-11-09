-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_5
-- name    : ExtremalForrelation.Nonadaptive.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:33.287987+00:00
-- url     : https://prove2.me/theorems/1e036914-f8d9-49da-a34c-08e024d2bd69
-- title:
--   Lemma 5 — Fourier dual identity $\widehat{\chi_f}=2^{-n/2}(-1)^s\chi_g$
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   For an instance of the construction (an $m$-dimensional $K$, a bijection $\pi$, bits $h$, a secret bit $s$, with $\bar h$ given by (1)), for every $y\in\mathbb F_2^n$,
--   $$\widehat{\chi_f}(y)=2^{-n/2}(-1)^s\chi_g(y).$$
--
--   It shows that $\chi_g$ is, up to the sign $(-1)^s$, the normalized Fourier transform of $\chi_f$; Corollary 1 follows.
--
--   Differences from the source:
--   - encoding: cosets C_1..C_M, D_1..D_M enumerated in a fixed way; π a uniform permutation of [M]; h : [M] → F_2 → cosets are the quotient types V⧸K and V⧸K^⊥; π a bijection V⧸K ≃ V⧸K^⊥; h a bit function on V⧸K; reason: transported along the fixed enumerations these are the same objects and the same uniform laws
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 5, p. 11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 5 (p. 11). For every `y ∈ 𝔽₂ⁿ`, `χ̂_f(y) = 2^{−n/2} (−1)^s χ_g(y)`. -/
theorem lemma_5 {n : ℕ} (hn : 4 ∣ n) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (h : V n ⧸ K → ZMod 2) (s : ZMod 2) (y : V n) :
    fourier (chi (fFun K π h)) y =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * (-1 : ℝ) ^ s.val * chi (gFun K π (hbarOf K π h s)) y := by sorry

end ExtremalForrelation.Nonadaptive
