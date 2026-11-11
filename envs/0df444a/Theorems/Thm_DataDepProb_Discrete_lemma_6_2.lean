-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_6_2
-- name    : DataDepProb.Discrete.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:11:36.571778+00:00
-- url     : https://prove2.me/theorems/824b8afb-5342-4803-9eaf-c5dd67d17be5
-- title:
--   Lemma 6.2 — the penalty $8H(p-e_s)^2$ satisfies (18), $K_0\le\log(1+d/n)$ and $EP_S(\tilde D)\le8\log^2(1+d/n)$
-- statement:
--   Let $n\ge1$. The penalty $P_s(p)=8H(p-e_s)^2$ of (17) is nonnegative, continuously differentiable and convex, vanishes at $e_s$, and satisfies
--   $$\mathrm{KL}(p\|q)^2\le P_s(p)+P_s(q),\qquad p,q\in\tilde\Delta_d .\qquad(18)$$
--   For every $D\in\Delta_d$ and i.i.d. input $S\sim D^n$, the output of the zero-update procedure $q_0(S)=e_S=(\hat D_S+u)/2$ satisfies
--   $$K_0=E\,\mathrm{KL}(\tilde D\|q_0(S))\le\log(1+d/n),\qquad E\,P_S(\tilde D)\le8\log^2(1+d/n).$$
--   With Lemma 6.1 (taking $\beta=2\sqrt2\log(1+d/n)$) this gives the rate of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: $n$ implicit → hypothesis $1\le n$; reason: $e_s$ is undefined for an empty sample.
--   - reading: "nonnegative, continuously differentiable, and convex" → on all of $\mathbb R^d$ (`∀ p`, `ContDiff ℝ 1`, `ConvexOn ℝ univ`); reason: $h$ is defined and $C^1$ on $\mathbb R$.
--   - encoding: expectations over $S\sim D^n$ → finite sums weighted by $D^n(s)$; reason: same expectation on a finite space.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 16, Lemma 6.2 (proof p. 17)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_MW

namespace DataDepProb.Discrete

/-- Lemma 6.2 (empirical moment bound, p. 16). Let `n ≥ 1`. For every sample `s ∈ [d]^n`, the
penalty `P_s(p) = 8H(p − e_s)²` of (17) is nonnegative, continuously differentiable and convex on
`ℝ^d`, vanishes at `e_s`, and satisfies `KL(p‖q)² ≤ P_s(p) + P_s(q)` for `p, q ∈ ∆̃_d` (18). For
every `D ∈ ∆_d` and `S ∼ D^n`, the zero-update output `q_0(S) = e_S = (D̂_S + u)/2` satisfies
`K_0 = E KL(D̃‖q_0(S)) ≤ log(1 + d/n)` and `E P_S(D̃) ≤ 8 log²(1 + d/n)`. -/
theorem lemma_6_2 {n d : ℕ} (hn : 1 ≤ n) :
    (∀ s : Fin n → Fin d,
      (∀ p, 0 ≤ penalty (eInit s) p) ∧ ContDiff ℝ 1 (penalty (eInit s)) ∧
      ConvexOn ℝ Set.univ (penalty (eInit s)) ∧ penalty (eInit s) (eInit s) = 0 ∧
      ∀ p ∈ truncSimplex d, ∀ q ∈ truncSimplex d,
        kl p q ^ 2 ≤ penalty (eInit s) p + penalty (eInit s) q) ∧
    ∀ D ∈ simplex d,
      ∑ s : Fin n → Fin d, sampleProb D s * kl (shift D) (eInit s)
          ≤ Real.log (1 + (d : ℝ) / n) ∧
      ∑ s : Fin n → Fin d, sampleProb D s * penalty (eInit s) (shift D)
          ≤ 8 * Real.log (1 + (d : ℝ) / n) ^ 2 := by sorry

end DataDepProb.Discrete
