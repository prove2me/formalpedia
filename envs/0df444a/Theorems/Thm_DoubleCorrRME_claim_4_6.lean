-- Prove2me | Theorems.Thm_DoubleCorrRME_claim_4_6
-- name    : DoubleCorrRME.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:11.779607+00:00
-- url     : https://prove2.me/theorems/1d7b29ef-74b4-4903-9ee7-f1c37fbf4a3b
-- title:
--   Claim 4.6, p.22 — fixed direction: $\|G_h\|_{L_p}\le O(\|h\|_2(1/\sqrt n+\sqrt{p/m}))$
-- statement:
--   Let $m=Nn$ with $N,n\ge1$, and let $v_1,\dots,v_m\in\mathbb R^d$ satisfy $\sum_kv_k=0$ and $\frac1m\sum_kv_kv_k^\top\preceq I_d$. Let $\pi$ be uniform on the permutations of $[m]$, $b_i=\frac1n\sum_{r=(i-1)n+1}^{in}v_{\pi(r)}$ and $G_h(\pi)=\frac1N\sum_i|\langle h,b_i\rangle|$. There is an absolute constant $C$ such that for every fixed $h\in\mathbb R^d$ and every $p\ge2$,
--
--   $$\|G_h\|_{L_p}\le C\,\|h\|_2\Big(\frac1{\sqrt n}+\sqrt{\frac pm}\Big).$$
--
--   This is the one-direction step of Lemma 4.5.
--
--   Differences from the source:
--   - encoding: the setting of the proof of Lemma 4.5 after "By rescaling, it is enough to prove the claim for κ = 1" → explicit hypotheses N, n ≥ 1, ∑_k v_k = 0 and (1/m)∑_k ⟨u, v_k⟩² ≤ ∥u∥² for all u; reason: the claim is stated inside that proof; the quadratic-form bound is equivalent to (1/m)∑_k v_k v_kᵀ ⪯ I_d
--   - encoding: O(·) → ∃ C > 0 before N, n, d, v, p (and h); reason: meaning of an absolute constant
--   - encoding: E and ∥·∥_{L_p} under a uniformly random permutation → finite averages permAvg, permLp over Equiv.Perm (Fin m); reason: the uniform law on a finite group; same values
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Claim 4.6 (proof of Lemma 4.5), p.22 (PDF p.23)

import Mathlib
import Definitions.Def_DoubleCorrRME_Perm

namespace DoubleCorrRME

/-- **Claim 4.6** (inside the proof of Lemma 4.5), p.22 (PDF p.23).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"For every fixed h ∈ ℝ^d and every p ≥ 2, ∥G_h∥_{L_p} ≤ O(∥h∥₂ (1/√n + √(p/m)))."

Setting (proof of Lemma 4.5, after "By rescaling, it is enough to prove the claim for κ = 1"):
`m = Nn`, `v_1, …, v_m ∈ ℝ^d` with `∑_k v_k = 0` and `(1/m)∑_k v_k v_kᵀ ⪯ I_d`, `π` uniform on the
permutations of `[m]`, `b_i := (1/n)∑_{r=(i−1)n+1}^{in} v_{π(r)}`, `G_h(π) := (1/N)∑_i |⟨h, b_i⟩|`.

**Formalization Note.**
* The constant is chosen before `N, n, d, v, h, p`. `N, n ≥ 1` (the users and the batch size of
  the paper).
* `(1/m)∑_k v_k v_kᵀ ⪯ I_d` is written as the quadratic-form bound
  `(1/m)∑_k ⟨u, v_k⟩² ≤ ‖u‖²` for all `u`, which is equivalent. -/
theorem claim_4_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → ∀ v : Fin (N * n) → Vec d,
        ∑ k, v k = 0 →
        (∀ u : Vec d, (1 / ((N : ℝ) * n)) * ∑ k, (inner ℝ u (v k)) ^ 2 ≤ ‖u‖ ^ 2) →
        ∀ (h : Vec d) (p : ℝ), 2 ≤ p →
          permLp (N * n) p (gH v h) ≤
            C * (‖h‖ * (1 / Real.sqrt n + Real.sqrt (p / ((N : ℝ) * n)))) := by sorry

end DoubleCorrRME
