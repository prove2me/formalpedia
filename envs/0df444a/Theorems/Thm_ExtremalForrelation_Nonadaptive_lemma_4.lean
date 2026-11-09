-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_4
-- name    : ExtremalForrelation.Nonadaptive.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:15.863477+00:00
-- url     : https://prove2.me/theorems/0d5baffd-b206-4a86-98f8-f24936e756e2
-- title:
--   Lemma 4 — queries in matched cosets give away the secret bit
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Let $K$ be an $m$-dimensional subspace, $\pi$ a bijection from the cosets of $K$ to those of $K^\perp$, $h$ a bit function on the cosets of $K$, $s$ a bit, and $f,g$ the functions of the construction, with $\bar h$ given by (1). For every coset $C$ of $K$, every $x\in C$ and every $y\in\pi(C)$,
--   $$g(y)=f(x)+\langle x,y\rangle+s .$$
--
--   This identity is the dependence between $h$ and $\bar h$ that encodes the secret bit; it gives equation (10).
--
--   Differences from the source:
--   - encoding: cosets C_1..C_M, D_1..D_M enumerated in a fixed way; π a uniform permutation of [M]; h : [M] → F_2 → cosets are the quotient types V⧸K and V⧸K^⊥; π a bijection V⧸K ≃ V⧸K^⊥; h a bit function on V⧸K; reason: transported along the fixed enumerations these are the same objects and the same uniform laws
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 4, p. 10, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 4 (p. 10). For every coset `C` of `K`, `x ∈ C` and `y ∈ π(C)`,
`g(y) = f(x) + ⟨x, y⟩ + s`, where `f`, `g` are the functions (2), (3) built from `K`, `π`, `h`
and `h̄` given by (1). -/
theorem lemma_4 {n : ℕ} (hn : 4 ∣ n) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (h : V n ⧸ K → ZMod 2) (s : ZMod 2) (x y : V n)
    (hxy : (Submodule.Quotient.mk y : V n ⧸ orth K) = π (Submodule.Quotient.mk x)) :
    gFun K π (hbarOf K π h s) y = fFun K π h x + dot x y + s := by sorry

end ExtremalForrelation.Nonadaptive
