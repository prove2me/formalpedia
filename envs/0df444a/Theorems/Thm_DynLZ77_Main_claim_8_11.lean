-- Prove2me | Theorems.Thm_DynLZ77_Main_claim_8_11
-- name    : DynLZ77.Main.claim_8_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:22:16.702027+00:00
-- url     : https://prove2.me/theorems/646eee0e-8d25-4b4d-8c19-3f3a9925bff7
-- title:
--   Claim 8.11 — aligned shifts of an irreducible occurrence give non-dominated points $(k+1, \ell-k)$
-- statement:
--   Let $i\in\mathrm{Ired}_S$, $\ell=\mathrm{LPF}'_S(i)$, and let $i'<i$ be a position with $S[i..i+\ell)=S[i'..i'+\ell)$. For every $k\in[0..\ell)$:
--   1. there is no position $j<i+k$ with $\mathrm{LCS}_S(i+k,j)\ge k+1$ and $\mathrm{LCP}_S(i+k,j)\ge\ell-k$ and one of the two inequalities strict;
--   2. $\mathrm{LCS}_S(i+k,i'+k)=k+1$ and $\mathrm{LCP}_S(i+k,i'+k)=\ell-k$.
--
--   Inside the proof of Lemma 1.2 this places the point $(k+1,\ell-k)$ among the non-dominated extension points counted by [BGK25, Lemma 17].
--
--   Differences from the source:
--   - reading: Ired_S = {1} ∪ {i > 1 | i + LPF′_S(i) ≠ i − 1 + LPF′_S(i − 1)} → Ired S ⊆ [1..|S|]: position 1 belongs to Ired_S only when |S| ≥ 1; reason: Ired_S is a set of positions of S ("irreducible LPF′ positions"); the empty string has no position 1, and with 1 ∈ Ired_ε the statement would be about a non-existent position
--   - encoding: an index i′ < i; an index j < i + k → 1 ≤ i′ < i; 1 ≤ j < i + k; reason: indices of S are positions 1, 2, …
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 51 (PDF 53), Claim 8.11 (proof of Lemma 1.2, §8.2)

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Claim 8.11** (p. 51). Let `i ∈ Ired_S`, `ℓ = LPF′_S(i)` and `i′ < i` with
`S[i..i + ℓ) = S[i′..i′ + ℓ)`. For every `k ∈ [0..ℓ)`: (1) no `j < i + k` has
`LCS_S(i + k, j) ≥ k + 1` and `LCP_S(i + k, j) ≥ ℓ − k` with one inequality strict;
(2) `LCS_S(i + k, i′ + k) = k + 1` and `LCP_S(i + k, i′ + k) = ℓ − k`. -/
theorem claim_8_11 {α : Type} [DecidableEq α] (S : List α) (i : ℕ) (hi : i ∈ Ired S) (ℓ : ℕ)
    (hℓ : ℓ = lpf' S i) (i' : ℕ) (hi'1 : 1 ≤ i') (hi' : i' < i)
    (heq : sub S i (i + ℓ - 1) = sub S i' (i' + ℓ - 1)) (k : ℕ) (hk : k < ℓ) :
    (¬ ∃ j : ℕ, 1 ≤ j ∧ j < i + k ∧ k + 1 ≤ lcsAt S (i + k) j ∧ ℓ - k ≤ lcpAt S (i + k) j ∧
        (k + 1 < lcsAt S (i + k) j ∨ ℓ - k < lcpAt S (i + k) j)) ∧
      lcsAt S (i + k) (i' + k) = k + 1 ∧ lcpAt S (i + k) (i' + k) = ℓ - k := by sorry

end DynLZ77.Main
