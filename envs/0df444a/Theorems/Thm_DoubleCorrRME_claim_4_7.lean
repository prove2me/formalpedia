-- Prove2me | Theorems.Thm_DoubleCorrRME_claim_4_7
-- name    : DoubleCorrRME.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:27.387672+00:00
-- url     : https://prove2.me/theorems/1540504a-f070-45f4-9e90-daec78c51d1c
-- title:
--   Claim 4.7, p.26 — all directions: $\|\sup_{u\in S^{d-1}}G_u\|_{L_p}\le O(1/\sqrt n+\sqrt{(d+p)/m})$
-- statement:
--   In the setting of Claim 4.6 (with $d\ge1$), there is an absolute constant $C$ such that for every $p\ge2$,
--
--   $$\Big\|\sup_{u\in S^{d-1}}G_u\Big\|_{L_p}\le C\Big(\frac1{\sqrt n}+\sqrt{\frac{d+p}m}\Big).$$
--
--   Together with Markov's inequality at $p=\max\{2,\log(1/q)\}$ this gives Lemma 4.5.
--
--   **Formalization Note** The supremum over the unit sphere is a real supremum of a family bounded by $\frac1N\sum_i\|b_i\|$.
--
--   Differences from the source:
--   - encoding: the setting of the proof of Lemma 4.5 after "By rescaling, it is enough to prove the claim for κ = 1" → explicit hypotheses N, n ≥ 1, ∑_k v_k = 0 and (1/m)∑_k ⟨u, v_k⟩² ≤ ∥u∥² for all u; reason: the claim is stated inside that proof; the quadratic-form bound is equivalent to (1/m)∑_k v_k v_kᵀ ⪯ I_d
--   - encoding: O(·) → ∃ C > 0 before N, n, d, v, p (and h); reason: meaning of an absolute constant
--   - encoding: E and ∥·∥_{L_p} under a uniformly random permutation → finite averages permAvg, permLp over Equiv.Perm (Fin m); reason: the uniform law on a finite group; same values
--   - encoding: sup_{u∈S^{d−1}} G_u → real ⨆ over Metric.sphere 0 1, with d ≥ 1; reason: the family is bounded above by (1/N)∑_i∥b_i∥, so the real supremum is the true one; d ≥ 1 makes the sphere nonempty
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Claim 4.7 (proof of Lemma 4.5), p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DoubleCorrRME_Perm

namespace DoubleCorrRME

/-- **Claim 4.7** (inside the proof of Lemma 4.5), p.26 (PDF p.27).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"For all p ≥ 2, we have ∥sup_{u∈S^{d−1}} G_u∥_{L_p} ≤ O(1/√n + √((d + p)/m))."

Setting as in Claim 4.6 (`κ = 1`): `m = Nn`, `∑_k v_k = 0`, `(1/m)∑_k v_k v_kᵀ ⪯ I_d`, `π` uniform,
`G_u(π) = (1/N)∑_i |⟨u, b_i(π)⟩|`.

**Formalization Note.**
* The constant is chosen before `N, n, d, v, p`; `N, n, d ≥ 1` (so `S^{d−1}` is nonempty).
* `sup_{u∈S^{d−1}} G_u(π)` is the real `⨆` over the unit sphere `Metric.sphere 0 1`; the family is
  bounded above by `(1/N)∑_i ‖b_i(π)‖`, so the real supremum is the true supremum.
* `⪯ I_d` is the quadratic-form bound, as in Claim 4.6. -/
theorem claim_4_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d → ∀ v : Fin (N * n) → Vec d,
        ∑ k, v k = 0 →
        (∀ u : Vec d, (1 / ((N : ℝ) * n)) * ∑ k, (inner ℝ u (v k)) ^ 2 ≤ ‖u‖ ^ 2) →
        ∀ p : ℝ, 2 ≤ p →
          permLp (N * n) p (fun π => ⨆ u : Metric.sphere (0 : Vec d) 1, gH v (u : Vec d) π) ≤
            C * (1 / Real.sqrt n + Real.sqrt (((d : ℝ) + p) / ((N : ℝ) * n))) := by sorry

end DoubleCorrRME
