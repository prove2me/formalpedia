-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_theorem_3_5
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:41:31.266111+00:00
-- url     : https://prove2.me/theorems/531ef742-df5f-464b-b3ea-e4ca464f8c66
-- title:
--   Theorem 3.5 — the zero-padded block tensor $T_n$ has border rank $\ge3n-11n^{3/4}$
-- statement:
--   Let $n\ge16$, and set
--
--   $$e=\lfloor n^{1/4}\rfloor,\qquad m=\Big\lfloor\frac{n}{e^2}\Big\rfloor.$$
--
--   Let $T_n\in(\mathbb C^n)^{\otimes3}$ be obtained by zero-padding the block tensor $T_{e,m}\in(\mathbb C^{me^2})^{\otimes3}$ of equation (3.2). Then its complex border rank satisfies
--
--   $$\underline R(T_n)\ge3n-11n^{3/4}.$$
--
--   This is Theorem 1.1 in more detail: it pins the specific explicit witness, while the mission goal only asserts that some polynomial-time explicit family exists. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: T_n obtained by zero-padding T_{e,m}, e = ⌊n^{1/4}⌋, m = ⌊n/e²⌋ → complexify (explicitFamily n) from the published Construction definition; reason: for n ≥ 16 explicitFamily n is exactly blockEntry (fourthRoot n) (n / fourthRoot n ^ 2), zero outside the me² × me² × me² block, and fourthRoot is the integer floor of the fourth root
--   - encoding: border rank R̲ → the published borderRank (least r with T in the closure of the rank ≤ r locus); reason: sequential limits and closure agree in finite-dimensional complex space
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Theorem 3.5, equation (3.3), p.11; T_{e,m} equation (3.2), p.9 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Construction

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Theorem 3.5, p.11. For n ≥ 16, with
e = ⌊n^{1/4}⌋ and m = ⌊n/e²⌋, the tensor T_n ∈ (ℂⁿ)^{⊗3} obtained by zero-padding T_{e,m}
(the published `explicitFamily n`, complexified) has border rank ≥ 3n − 11 n^{3/4}. -/
theorem theorem_3_5 (n : ℕ) (hn : 16 ≤ n) :
    3 * (n : ℝ) - 11 * (n : ℝ) ^ ((3 : ℝ) / 4) ≤
      (borderRank (complexify (explicitFamily n)) : ℝ) := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
