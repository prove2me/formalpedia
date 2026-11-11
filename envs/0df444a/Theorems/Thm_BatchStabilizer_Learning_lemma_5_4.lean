-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_5_4
-- name    : BatchStabilizer.Learning.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:42.269215+00:00
-- url     : https://prove2.me/theorems/cb88c942-dfbe-4ae3-a2aa-375a5092a2fa
-- title:
--   Lemma 5.4 — Chang-type dimension bound for strongly biased parities
-- statement:
--   Let $\nu$ be a probability distribution on $\mathbb F_2^n$ with $\nu(u)\le c/2^n$ for all $u$, where $c\ge1$, and let $0<\epsilon<1$. Then
--   $$\dim\operatorname{span}\{x\neq0:|\hat\nu(x)|>\epsilon\}\le\frac{\log_2c}{1-H_2\big((1-\epsilon)/2\big)},$$
--   where $\hat\nu(x)=\sum_u\nu(u)(-1)^{x\cdot u}$ and $H_2$ is the binary entropy in bits. The threshold $\epsilon$ is independent of the learner's accuracy. This abstract statement involves no quantum state.
--
--   Differences from the source:
--   - encoding: the binary entropy H₂(p) = −p log₂ p − (1−p) log₂(1−p) → Real.binEntropy p / Real.log 2; reason: the same function, with 0 log 0 = 0
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 19 (PDF p. 20), Lemma 5.4, equation (68)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 5.4, printed p. 19 (PDF p. 20): a Chang-type bound.  If `ν` is a probability
distribution on `F₂ⁿ` with `ν(u) ≤ c/2ⁿ`, `c ≥ 1`, then for `0 < ϵ < 1`,
`dim span{x ≠ 0 : |ν̂(x)| > ϵ} ≤ log₂ c/(1 - H₂((1-ϵ)/2))` (68). -/
theorem lemma_5_4 {n : ℕ} (ν : (Fin n → ZMod 2) → ℝ) (hν0 : ∀ u, 0 ≤ ν u)
    (hν1 : ∑ u, ν u = 1) (c : ℝ) (hc : 1 ≤ c) (hνc : ∀ u, ν u ≤ c / 2 ^ n)
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) :
    (Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) {x : Fin n → ZMod 2 | x ≠ 0 ∧ ϵ < |binFourier ν x|}) : ℝ) ≤
      Real.logb 2 c / (1 - H2 ((1 - ϵ) / 2)) := by sorry

end BatchStabilizer.Learning
