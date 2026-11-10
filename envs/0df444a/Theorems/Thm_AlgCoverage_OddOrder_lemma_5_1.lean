-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_lemma_5_1
-- name    : AlgCoverage.OddOrder.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:19.641694+00:00
-- url     : https://prove2.me/theorems/5f9a4bd7-41b9-4c3f-8095-03097cf52b47
-- title:
--   Lemma 5.1 — dimension-uniform full-support bound $B(T,D)b^n$, raw-array count, and nononto bound $A(T,D)2^{-n}$
-- statement:
--   Let $F$ be a field of odd characteristic, $T\ge3$ a maximum arity, $1\le d\le D$, and $U_1,\dots,U_n\in GL_d(F)$ any common stream fixed before the independent fair selector bits. With the constants (5.2) and $b=31/64$, uniformly over the stream:
--   for $3\le j\le T$,
--   $$\Pr\big(F^{\rm fs}_{j,d}(n)\big)\le B(T,D)\,b^n, \tag{5.3}$$
--   and the number of raw binary $j\times n$ arrays in this event is at most $B(T,D)\,2^{n(j-1)}(31/32)^n$ (5.4); for every $j\le T$ the unrestricted nononto event satisfies
--   $$\Pr(\text{not onto})\le A(T,D)\,2^{-n}. \tag{5.5}$$
--   The proof is in Appendix B of the paper. These bounds feed the averaged good-mass deficit (7.5) and the witness counts (8.3).
--
--   Differences from the source:
--   - encoding: U_i ∈ GL_d(F), block matrices and covectors → Matrix.GeneralLinearGroup (Fin d) F, Matrix.mulVec / Matrix.vecMul; reason: standard matrix encoding; same objects
--   - encoding: field F of odd characteristic → Odd (ringChar F); reason: the characteristic of a field is 0 or a prime; Odd excludes 0 and 2, leaving exactly the odd primes
--   - encoding: probability over independent fair selector bits (empty and repeated rows allowed) → probBits: counting ratio over all raw arrays Fin j → Fin n → Bool, divided by 2^{jn}; reason: independent fair bits are the uniform law on {0,1}^{j×n}; same numbers
--   - encoding: L = ⌈ln(T+2)⌉, τ = 4⌈log₂(T+2)⌉ + 16 → natural-number ceilings Nat.ceil of these positive reals; reason: the arguments are positive, so Nat.ceil is the ceiling
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 18 (PDF 19), Lemma 5.1, Eqs. (5.3)–(5.5); proof App. B, pp. 36–39 (PDF 37–40)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_CommonStream

namespace AlgCoverage.OddOrder

/-- Lemma 5.1, Lin, printed p. 18 / PDF 19 (proved in Appendix B). Field `F` of odd characteristic,
maximum arity `T ≥ 3`, dimension `1 ≤ d ≤ D`, and any common stream `U₁, …, U_n ∈ GL_d(F)` fixed before
the independent fair bits: for `3 ≤ j ≤ T`, `Pr(F^fs_{j,d}(n)) ≤ B(T,D) b^n` (5.3) and the number of raw
binary arrays in this event is at most `B(T,D) 2^{n(j−1)} (31/32)^n` (5.4); for every `j ≤ T`,
`Pr(not onto) ≤ A(T,D) 2^{−n}` (5.5). Constants (5.2). -/
theorem lemma_5_1 {F : Type*} [Field F] (hF : Odd (ringChar F)) (T D d n : ℕ) (hT : 3 ≤ T)
    (hd : 1 ≤ d) (hdD : d ≤ D) (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F) :
    (∀ j : ℕ, 3 ≤ j → j ≤ T →
      probBits j n (FullSupport (j := j) U) ≤ envB T D * constB_small ^ n) ∧
    (∀ j : ℕ, 3 ≤ j → j ≤ T →
      (Nat.card {v : Fin j → Fin n → Bool // FullSupport U v} : ℝ) ≤
        envB T D * (2 : ℝ) ^ (n * (j - 1)) * (31 / 32 : ℝ) ^ n) ∧
    (∀ j : ℕ, j ≤ T →
      probBits j n (NotOnto (j := j) U) ≤ envA T D * (2 : ℝ) ^ (-(n : ℤ))) := by sorry

end AlgCoverage.OddOrder
