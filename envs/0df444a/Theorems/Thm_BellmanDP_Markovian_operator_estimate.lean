-- Prove2me | Theorems.Thm_BellmanDP_Markovian_operator_estimate
-- name    : BellmanDP.Markovian.operator_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T21:35:52.29082+00:00
-- url     : https://prove2.me/theorems/675d072c-b114-49bf-9f2f-7a865575007f
-- title:
--   Chapter XI, § 4, Lemma — the difference estimate for maximized integral operators
-- statement:
--   Fix $t \ge 0$. For each row $i = 1, \dots, N$ let $S_i$ be a set of admissible parameters (for instance, functions of time), and for $q_i \in S_i$ let $a_{ij}(q_i, s)$ be integrable over $[0,t]$ and $b^{(1)}_i(q_i), b^{(2)}_i(q_i)$ real numbers (the values $b_1(q,t)$, $b_2(q,t)$ at the fixed $t$). Let $x(s), y(s) \in \mathbb R^N$ be continuous on $[0,t]$. Define, row by row, the maxima (assumed attained)
--   $$T_1(x)_i = \max_{q_i \in S_i}\Big[b^{(1)}_i(q_i) + \int_0^t \sum_j a_{ij}(q_i,s)\, x_j(s)\, ds\Big],\quad T_2(y)_i = \max_{q_i \in S_i}\Big[b^{(2)}_i(q_i) + \int_0^t \sum_j a_{ij}(q_i,s)\, y_j(s)\, ds\Big].$$
--   With the norms $\|x\| = \sum_i |x_i|$ and $\|A\| = \sum_{i,j} |a_{ij}|$ of (3.5), there is an admissible joint parameter $q = (q_1,\dots,q_N)$ with
--   $$\|T_1(x) - T_2(y)\| \le \|b_1(q,t) - b_2(q,t)\| + \int_0^t \|A(q,s)\|\, \|x(s) - y(s)\|\, ds ,$$
--   which is Bellman's inequality (4.5), whose right-hand side is a maximum over $q$.
--
--   Bellman calls this lemma "the fulcrum of our existence and uniqueness proof": it gives the contraction estimate behind Theorems 1 and 4.
--
--   **Formalization Note** "$\le \max_q [\dots]$" is stated as "$\le [\dots]$ at some admissible $q$", which is equivalent whenever the maximum exists and does not need it to. Integrability of the coefficients and continuity of $x, y$ are assumed so that the integrals are genuine.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, § 4, Lemma, Eqs. (4.4)-(4.5), p. 321; norms (3.5), p. 320

import Mathlib

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, § 4, Lemma, p. 321. For row-wise parameters `q`
(elements of arbitrary sets `S i`, e.g. sets of functions of time) and a fixed `t ≥ 0`, let
`T₁(x)_i = Max_q [b₁_i(q, t) + ∫_0^t Σ_j a_ij(q, s) x_j(s) ds]` and
`T₂(y)_i = Max_q [b₂_i(q, t) + ∫_0^t Σ_j a_ij(q, s) y_j(s) ds]`, the maxima attained. Then, with
`‖x‖ = Σ_i |x_i|` and `‖A‖ = Σ_{i,j} |a_ij|` (3.5),
`‖T₁(x) − T₂(y)‖ ≤ Max_q [‖b₁(q, t) − b₂(q, t)‖ + ∫_0^t ‖A(q, s)‖ ‖x(s) − y(s)‖ ds]`;
stated as: the right-hand side is at least the left-hand side for some admissible joint `q`. -/
theorem operator_estimate {N : ℕ} {P : Fin N → Type*}
    (a : (i : Fin N) → P i → ℝ → Fin N → ℝ) (b₁ b₂ : (i : Fin N) → P i → ℝ)
    (S : (i : Fin N) → Set (P i)) (t : ℝ) (ht : 0 ≤ t)
    (x y : ℝ → Fin N → ℝ) (hx : ContinuousOn x (Set.Icc 0 t)) (hy : ContinuousOn y (Set.Icc 0 t))
    (ha : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N,
      MeasureTheory.IntegrableOn (fun s => a i q s j) (Set.Icc 0 t))
    (T₁ T₂ : Fin N → ℝ)
    (hT₁ : ∀ i : Fin N, IsGreatest
      ((fun q => b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) '' S i) (T₁ i))
    (hT₂ : ∀ i : Fin N, IsGreatest
      ((fun q => b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j) '' S i) (T₂ i)) :
    ∃ q ∈ Set.pi Set.univ S,
      ∑ i, |T₁ i - T₂ i| ≤
        ∑ i, |b₁ i (q i) - b₂ i (q i)| +
          ∫ s in (0 : ℝ)..t, (∑ i, ∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j| := by sorry

end BellmanDP.Markovian
