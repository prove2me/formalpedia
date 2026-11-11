-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_14
-- name    : DenseMatching.IPM.lemma_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:02.056201+00:00
-- url     : https://prove2.me/theorems/d4a74e56-cfac-46a5-8e74-e7769599cfff
-- title:
--   Lemma 4.14 — the initial point f_e = 2/n, µ₀ = 21/n is eligible, feasible, and has |ν_e| ≤ 10/21
-- statement:
--   On $K_{n/2,n/2}$ ($n=2k\ge2^{20}$), for costs $c\in[10,11]^E$, the point $f_e=2/n$ with target $\mu_0=21/n$ is eligible (Definition 4.1), satisfies $B^\top f=d$, and its deviations $\nu_e=10(\mu_e/\mu_0-1)$, $\mu_e=f_ec_e$, satisfy
--   $$|\nu_e|\le\tfrac{10}{21}<\tfrac12\quad\text{for every edge}.$$
--   It is the starting point of the method in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 50, Lemma 4.14

import Mathlib
import Definitions.Def_DenseMatching_IPM_FlowLP

open Matrix

namespace DenseMatching.IPM

/-- Lemma 4.14 (p. 50). On `K_{n/2,n/2}` (`n = 2k ≥ 2^20`), for costs `c ∈ [10, 11]^E`, the point
`f_e = 2/n`, `μ₀ = 21/n` is eligible, `B⊤f = d`, and the deviations `ν_e = 10(μ_e/μ₀ − 1)` satisfy
`|ν_e| ≤ 10/21 < 1/2` for every edge. -/
theorem lemma_4_14 (k : ℕ) (hk : 2 ^ 19 ≤ k) (c : KE k → ℝ) (hc : ∀ e, 10 ≤ c e ∧ c e ≤ 11) :
    let n : ℝ := 2 * k
    let f : KE k → ℝ := fun _ => 2 / n
    Eligible k f c (21 / n) ∧ (incK k)ᵀ *ᵥ f = demand k ∧
      (∀ e, |deviation (21 / n) f c e| ≤ 10 / 21) ∧ (10 : ℝ) / 21 < 1 / 2 := by sorry

end DenseMatching.IPM
