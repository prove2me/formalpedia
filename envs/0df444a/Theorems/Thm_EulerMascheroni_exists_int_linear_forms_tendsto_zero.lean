-- Prove2me | Theorems.Thm_EulerMascheroni_exists_int_linear_forms_tendsto_zero
-- name    : EulerMascheroni.exists_int_linear_forms_tendsto_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-10T21:22:23.931785+00:00
-- url     : https://prove2.me/theorems/7cfdfd24-8781-4193-a881-93684053aa63
-- title:
--   Vanishing integer linear forms in $\gamma$
-- statement:
--   There exist sequences of integers $(p_n)_{n\ge 0}$ and $(q_n)_{n\ge 0}$, with $q_n > 0$, whose associated linear forms in Euler's constant
--
--   $$L_n \;=\; q_n \gamma - p_n$$
--
--   never vanish and tend to $0$ as $n \to \infty$.
--
--   This is the Diophantine input that the classical irrationality criterion asks for: together with that criterion it yields the irrationality of $\gamma$, and it is the exact point at which every known attack stalls. Explicit constructions of linear forms in $\gamma$ do exist. Aptekarev's multiple-orthogonal-polynomial construction produces integers $p_n, q_n$ with
--
--   $$\gamma - \frac{p_n}{q_n} \;=\; -2\pi e^{-2\sqrt{2n}}\Big(1 + O\big(n^{-1/2}\big)\Big), \qquad q_n \;=\; (2n)!\,\frac{e^{\sqrt{2n}}}{\sqrt[4]{n}}\Big(\tfrac{1}{\sqrt{\pi}(4e)^{3/8}} + O\big(n^{-1/2}\big)\Big),$$
--
--   and the Hessami Pilehrood construction $q_n = \sum_{k=0}^n \binom{n}{k}^2 k!$, $p_n = \sum_{k=0}^n \binom{n}{k}^2 k!\,(2H_{n-k} - H_k)$ gives $\gamma - p_n/q_n = -e^{-4\sqrt{n}}(2\pi + O(n^{-1/2}))$. In both cases the denominators grow factorially while the error decays only like $e^{-c\sqrt{n}}$, so the products $q_n\gamma - p_n$ diverge rather than vanish; the approximations are of insufficient quality to certify irrationality. Producing any admissible pair of sequences — by these methods or others — is open.
--
--   **Formalization note.** `Real.eulerMascheroniConstant` is Mathlib's $\gamma$. The positivity requirement $q_n > 0$ is a normalization and costs nothing: replacing $(p_n, q_n)$ by $(-p_n, -q_n)$ changes only the sign of the form, and indices with $q_n = 0$ may be discarded.
-- source:
--   Open problem; the standard reformulation of the irrationality of Euler's constant. A. I. Aptekarev, On linear forms containing the Euler constant, https://arxiv.org/abs/0902.1768; Kh. and T. Hessami Pilehrood, On a continued fraction expansion for Euler's constant (2013); survey: J. Lagarias, Euler's constant: Euler's work and modern developments, Bull. Amer. Math. Soc. 50 (2013), https://arxiv.org/abs/1303.1856, Section 3.15 (Theorems 3.15.2-3.15.3) and Section 5.

import Mathlib

open Real

namespace EulerMascheroni
theorem exists_int_linear_forms_tendsto_zero :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
      Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
        Filter.atTop (nhds 0) := by sorry
end EulerMascheroni
