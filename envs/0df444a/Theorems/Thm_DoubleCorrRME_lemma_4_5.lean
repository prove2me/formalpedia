-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_4_5
-- name    : DoubleCorrRME.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:24.578831+00:00
-- url     : https://prove2.me/theorems/75f06382-9259-4a34-8d77-9495da81cac3
-- title:
--   Lemma 4.5, p.22 — random batch means: $\sup_u\frac1N\sum_i|\langle u,b_i\rangle|\le O(\sqrt\kappa(1/\sqrt n+\sqrt{(d+\log(1/q))/m}))$ w.p. $1-q$
-- statement:
--   Let $m=Nn$ with $N,n\ge1$, and let $v_1,\dots,v_m\in\mathbb R^d$ be deterministic vectors with
--
--   $$\sum_{k=1}^mv_k=0_d,\qquad \frac1m\sum_{k=1}^mv_kv_k^\top\preceq\kappa I_d .$$
--
--   Let $\pi$ be uniform on the permutations of $[m]$ and $b_i=\frac1n\sum_{r=(i-1)n+1}^{in}v_{\pi(r)}$ for $i\in[N]$. There is an absolute constant $C$ such that for every $q\in(0,1)$, with probability at least $1-q$,
--
--   $$\sup_{u\in S^{d-1}}\frac1N\sum_{i=1}^N|\langle u,b_i\rangle|\le C\sqrt\kappa\Big(\frac1{\sqrt n}+\sqrt{\frac{d+\log(1/q)}m}\Big).$$
--
--   Applied to the truncated samples, this shows that the truncated batch means keep the $1/\sqrt n$ averaging gain.
--
--   **Formalization Note** The probability is a ratio of cardinalities of permutation sets.
--
--   Differences from the source:
--   - encoding: q (implicit), N, n → 0 < q < 1, 1 ≤ N, 1 ≤ n; reason: q is a failure probability; N, n are the numbers of users and samples
--   - encoding: (1/m)∑_k v_k v_kᵀ ⪯ κI_d → (1/m)∑_k ⟨u, v_k⟩² ≤ κ∥u∥² for all u; reason: equivalent quadratic-form statement
--   - encoding: O(·) → ∃ C > 0 before N, n, d, κ, v, q; reason: meaning of an absolute constant
--   - encoding: "with probability at least 1 − q" over a uniform permutation → the fraction of permutations satisfying the bound is ≥ 1 − q; reason: the uniform law on a finite set
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.5, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_DoubleCorrRME_Perm

namespace DoubleCorrRME

open Classical in
/-- **Lemma 4.5**, p.22 (PDF p.23).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let m = Nn, and let v_1, …, v_m ∈ ℝ^d be deterministic vectors such that ∑_{k=1}^m v_k = 0_d, and
(1/m)∑_{k=1}^m v_k v_kᵀ ⪯ κI_d. Let π be uniform on the permutations of [m], and for all i ∈ [N], we
define b_i := (1/n)∑_{r=(i−1)n+1}^{in} v_{π(r)}. Then, with probability at least 1 − q,
sup_{u∈S^{d−1}} (1/N)∑_{i=1}^N |⟨u, b_i⟩| ≤ O(√κ (1/√n + √((d + log(1/q))/m)))."

**Formalization Note.**
* The constant is chosen before `N, n, d, κ, v, q`. `N, n ≥ 1`; `q ∈ (0, 1)` (a probability).
* `⪯ κI_d` is the quadratic-form bound `(1/m)∑_k ⟨u, v_k⟩² ≤ κ‖u‖²`. No sign condition on `κ` is
  needed: for `d ≥ 1` the bound forces `κ ≥ 0`, and for `d = 0` the sphere is empty.
* "sup_{u∈S^{d−1}} … ≤ X" is "for every unit `u`, … ≤ X". The probability is the uniform measure of a
  finite set of permutations, a ratio of cardinalities. -/
theorem lemma_4_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → ∀ (κ : ℝ) (v : Fin (N * n) → Vec d),
        ∑ k, v k = 0 →
        (∀ u : Vec d, (1 / ((N : ℝ) * n)) * ∑ k, (inner ℝ u (v k)) ^ 2 ≤ κ * ‖u‖ ^ 2) →
        ∀ q : ℝ, 0 < q → q < 1 →
          1 - q ≤
            ((Finset.univ.filter fun π : Equiv.Perm (Fin (N * n)) =>
                ∀ u : Vec d, ‖u‖ = 1 →
                  ((N : ℝ))⁻¹ * ∑ i, |inner ℝ u (batchMean v π i)| ≤
                    C * (Real.sqrt κ * (1 / Real.sqrt n +
                      Real.sqrt (((d : ℝ) + Real.log (1 / q)) / ((N : ℝ) * n))))).card : ℝ) /
              (Fintype.card (Equiv.Perm (Fin (N * n))) : ℝ) := by sorry

end DoubleCorrRME
