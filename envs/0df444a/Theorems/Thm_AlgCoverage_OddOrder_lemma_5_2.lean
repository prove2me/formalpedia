-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_lemma_5_2
-- name    : AlgCoverage.OddOrder.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:10.550957+00:00
-- url     : https://prove2.me/theorems/2ffdd519-06ee-4a0b-9096-a390034ecedb
-- title:
--   Lemma 5.2 — scalar full-support bound $\Pr(F^{\rm fs}_{j,1}(n))\le(40/7)^{j-1}(31/64)^n$, and the scalar envelopes (5.7)
-- statement:
--   Let $F$ be a field of odd characteristic and $U_1,\dots,U_n\in F^\times$ a common stream fixed before the independent fair selector bits (the case $d=1$ of §5). Allowing empty and repeated rows, for every $j\ge3$
--   $$\Pr\big(F^{\rm fs}_{j,1}(n)\big)\le(40/7)^{j-1}(31/64)^n. \tag{5.6}$$
--   Moreover, for every maximum arity $T\ge3$, the three bounds of Lemma 5.1 hold in the scalar case with the envelopes $B_{\rm sc}(T)=(40/7)^{T-1}$, $A_{\rm sc}(T)=2T^2+2TB_{\rm sc}(T)$ (5.7): for $3\le j\le T$, $\Pr(F^{\rm fs}_{j,1}(n))\le B_{\rm sc}(T)b^n$ with $b=31/64$ and the number of raw binary arrays in this event is at most $B_{\rm sc}(T)2^{n(j-1)}(31/32)^n$; and for every $j\le T$, $\Pr(\text{not onto})\le A_{\rm sc}(T)2^{-n}$.
--
--   This is the short scalar route used for groups with prime-order layers.
--
--   Differences from the source:
--   - encoding: scalar stream U_i ∈ F^× → U_i ∈ GL₁(F) (invertible 1×1 matrices); reason: F^× ≅ GL₁(F) and the block map is the same
--   - encoding: field F of odd characteristic → Odd (ringChar F); reason: the characteristic of a field is 0 or a prime; Odd excludes 0 and 2, leaving exactly the odd primes
--   - encoding: probability over independent fair selector bits (empty and repeated rows allowed) → probBits: counting ratio over all raw arrays Fin j → Fin n → Bool, divided by 2^{jn}; reason: independent fair bits are the uniform law on {0,1}^{j×n}; same numbers
--   - reading: 'For all arities at most T ≥ 3, Lemma 5.1 may therefore be used with B_sc(T), A_sc(T)' → the three conclusions (5.3), (5.4), (5.5) of Lemma 5.1 hold for d = 1 with B(T,D), A(T,D) replaced by B_sc(T), A_sc(T); reason: this is how (5.9) uses the scalar envelopes
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 19 (PDF 20), Lemma 5.2, Eqs. (5.6)–(5.7)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_CommonStream

namespace AlgCoverage.OddOrder

/-- Lemma 5.2 (scalar full-support bound), Lin, printed p. 19 / PDF 20. Scalar case `d = 1` (a
stream `U₁, …, U_n ∈ F^× = GL₁(F)`, fixed before the bits), `j ≥ 3`, empty and repeated rows allowed:
`Pr(F^fs_{j,1}(n)) ≤ (40/7)^{j−1} (31/64)^n` (5.6); and for every maximum arity `T ≥ 3` the three
bounds of Lemma 5.1 hold in the scalar case with `B_sc(T) = (40/7)^{T−1}`,
`A_sc(T) = 2T² + 2T B_sc(T)` (5.7). -/
theorem lemma_5_2 {F : Type*} [Field F] (hF : Odd (ringChar F)) (n : ℕ)
    (U : Fin n → Matrix.GeneralLinearGroup (Fin 1) F) :
    (∀ j : ℕ, 3 ≤ j →
      probBits j n (FullSupport (j := j) U) ≤ (40 / 7 : ℝ) ^ (j - 1) * (31 / 64 : ℝ) ^ n) ∧
    ∀ T : ℕ, 3 ≤ T →
      (∀ j : ℕ, 3 ≤ j → j ≤ T →
        probBits j n (FullSupport (j := j) U) ≤ envBsc T * constB_small ^ n) ∧
      (∀ j : ℕ, 3 ≤ j → j ≤ T →
        (Nat.card {v : Fin j → Fin n → Bool // FullSupport U v} : ℝ) ≤
          envBsc T * (2 : ℝ) ^ (n * (j - 1)) * (31 / 32 : ℝ) ^ n) ∧
      (∀ j : ℕ, j ≤ T →
        probBits j n (NotOnto (j := j) U) ≤ envAsc T * (2 : ℝ) ^ (-(n : ℤ))) := by sorry

end AlgCoverage.OddOrder
