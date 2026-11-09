-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_corollary_1
-- name    : ExtremalForrelation.Nonadaptive.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:58.296027+00:00
-- url     : https://prove2.me/theorems/94cdfad0-6a93-4987-8f4d-0783de8745fe
-- title:
--   Corollary 1 — both functions are bent and $\mathrm{forr}(\chi_f,\chi_g)=(-1)^s$
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   For every instance of the construction with secret bit $s$, both $\chi_f$ and $\chi_g$ are bent functions, and
--   $$\mathrm{forr}(\chi_f,\chi_g)=(-1)^s .$$
--
--   So $s=0$ gives a yes-instance and $s=1$ a no-instance of extremal Forrelation: the hard distribution satisfies the promise.
--
--   Differences from the source:
--   - encoding: cosets C_1..C_M, D_1..D_M enumerated in a fixed way; π a uniform permutation of [M]; h : [M] → F_2 → cosets are the quotient types V⧸K and V⧸K^⊥; π a bijection V⧸K ≃ V⧸K^⊥; h a bit function on V⧸K; reason: transported along the fixed enumerations these are the same objects and the same uniform laws
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Corollary 1, p. 11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Corollary 1 (p. 11). Both `χ_f` and `χ_g` are bent, and `forr(χ_f, χ_g) = (−1)^s`. -/
theorem corollary_1 {n : ℕ} (hn : 4 ∣ n) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (π : (V n ⧸ K) ≃ (V n ⧸ orth K))
    (h : V n ⧸ K → ZMod 2) (s : ZMod 2) :
    IsBent (chi (fFun K π h)) ∧ IsBent (chi (gFun K π (hbarOf K π h s))) ∧
      forr (chi (fFun K π h)) (chi (gFun K π (hbarOf K π h s))) = (-1 : ℝ) ^ s.val := by sorry

end ExtremalForrelation.Nonadaptive
