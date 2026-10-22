-- Prove2me | Theorems.Thm_ChoiceCDLP_MNL_sorted_prefix_optimal
-- name    : ChoiceCDLP.MNL.sorted_prefix_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:59:07.969984+00:00
-- url     : https://prove2.me/theorems/782f82d9-82e9-45cd-a7b2-7f2c8f15c149
-- title:
--   Proof of Proposition 6 — for sorted scores w_1 ≥ ⋯ ≥ w_s, a prefix z* = (v_1, …, v_{i*}, 0, …, 0) is optimal for (17) (repaired: some w_i ≥ 0)
-- statement:
--   Let $s \in \mathbb{N}$, let $v_1, \dots, v_s > 0$, $v_0 \ge 0$, and let the scores be sorted, $w_1 \ge w_2 \ge \cdots \ge w_s$, with at least one $w_i \ge 0$. Then there is an index $i^*$ with $1 \le i^* \le s$ such that
--   $$z^*_i = \begin{cases} v_i & i \le i^*,\\ 0 & i > i^*\end{cases}$$
--   is an optimal solution of
--   $$\max_{z \in \prod_{i}[0, v_i]} \; \frac{\sum_{i=1}^s w_i z_i}{\sum_{i=1}^s z_i + v_0},$$
--   that is, $z^*$ lies in the box and $h(z) \le h(z^*)$ for every $z$ in the box.
--
--   In words: after sorting the products by score, it is optimal to offer a top segment of the ranking in full and nothing else. This is the relaxed form of Proposition 6.
--
--   **Formalization Note.** Indices are `Fin s` (0-based), so $i^*$ is an element of `Fin s`; "$1 \le i^* \le s$" becomes "$i^*$ exists in `Fin s`", which forces $s \ge 1$. *Repair:* the hypothesis "some $w_i \ge 0$" is added. As printed (with $1 \le i^*$) the claim is false when every $w_i < 0$: for $s = 1$, $w_1 = -1$, $v_1 = 1$, $v_0 = 1$, the only candidate $z^* = v_1 = 1$ has value $-1/2$, while $z = 0$ has value $0$. The paper's use of the result allows negative scores ($w_j = r_j - \pi^\top A_j$, p. 300), so the case is not vacuous. The conclusion asserts that $z^*$ is *an* optimal solution: with ties several optima exist, and an optimum can even be interior, so "the optimal solution" is not claimed to be unique.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 309, Appendix, proof of Proposition 6 (the nested optimal solution z*, 1 ≤ i* ≤ s)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_relaxedObjective

namespace ChoiceCDLP.MNL

/-- Proof of Proposition 6 (p. 309): with the scores sorted, `w_1 ≥ w_2 ≥ ⋯ ≥ w_s`, an optimal
solution of the relaxation `max_{z ∈ ∏_i [0, v_i]} (∑_i w_i z_i) / (∑_i z_i + v₀)` is
`z*_i = v_i` for `i ≤ i*` and `z*_i = 0` for `i > i*`, for some `1 ≤ i* ≤ s`.
Indices are `Fin s` (0-based), so `i* : Fin s`. Repaired (the paper's `1 ≤ i*` fails when
every `w_i < 0`, where `z = 0` is the only optimum): the hypothesis that some `w_i ≥ 0` is
added. The conclusion asserts that `z*` is *an* optimal solution: it lies in the box and
no point of the box has a larger objective value. -/
theorem sorted_prefix_optimal (s : ℕ) (v w : Fin s → ℝ) (v₀ : ℝ)
    (hv : ∀ i, 0 < v i) (hv₀ : 0 ≤ v₀) (hw : Antitone w) (hw_nonneg : ∃ i, 0 ≤ w i) :
    ∃ istar : Fin s, (fun i => if i ≤ istar then v i else 0) ∈ Set.Icc 0 v ∧
      ∀ z ∈ Set.Icc 0 v,
        relaxedObjective w v₀ z ≤
          relaxedObjective w v₀ (fun i => if i ≤ istar then v i else 0) := by sorry

end ChoiceCDLP.MNL
