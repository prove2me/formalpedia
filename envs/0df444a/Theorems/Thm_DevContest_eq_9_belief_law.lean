-- Prove2me | Theorems.Thm_DevContest_eq_9_belief_law
-- name    : DevContest.eq_9_belief_law
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:28.810859+00:00
-- url     : https://prove2.me/theorems/8f1e8364-376a-4ddb-8107-f5b2d3b8ae8b
-- title:
--   Display (9) — the law of motion of the belief
-- statement:
--   Let $x_0,x_1,\phi:[0,\infty)\to[0,1]$ be measurable, and let $\lambda>0$. Let $m_0,m_1$ be continuous on $[0,\infty)$, with $m_0(0)>0$, $m_1(0)\ge0$, solving
--   $$
--   m_0'=-\lambda x_0m_0,\qquad m_1'=\lambda x_0(1-\phi)m_0-\lambda x_1m_1 .
--   $$
--   Here $m_0$ is the mass of the rival being in the first stage, and $m_1$ the mass of her being in the second stage with her success undisclosed. Then $m_0+m_1>0$ at every date, $p=m_1/(m_0+m_1)\in[0,1]$, and
--   $$
--   dp_t=(1-p_t)\bigl[x_{0,t}\lambda-p_tx_{1,t}\lambda-(1-p_t)x_{0,t}\lambda\phi_t\bigr]dt .
--   $$
--   This is how an agent with no success updates her belief about her rival, for any efforts and disclosure rates.
--
--   **Formalization Note** The efforts are only measurable, so the equations for the masses and for $p$ hold in integral form.
--
--   Differences from the source:
--   - encoding: the limit $dt\to0$ of the Bayes formula on p.ec17, written as a differential → the integral equations of the masses $m_0,m_1$ and of $p=m_1/(m_0+m_1)$; reason: the efforts are only measurable; the Bayes formula's numerator and denominator are the masses
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, display (9), p.21; Bayes step, p.ec17

import Mathlib
import Definitions.Def_DevContest_firstStageObjective

open MeasureTheory

namespace DevContest

/-- Display (9), Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author manuscript,
p.21, derived from the Bayes step on p.ec17: let `m0`, `m1` be the masses of the rival being in the
first stage, and in the second stage with her success undisclosed, for measurable efforts `x0`, `x1`
and disclosure probability `φ`. Then `p = m1 / (m0 + m1)` is a well-defined belief and it satisfies
`dp = (1 - p) [x0 λ - p x1 λ - (1 - p) x0 λ φ] dt`.

**Formalization Note.** The efforts are only measurable, so the mass equations and (9) are stated
in integral form. The masses are unnormalized: the total mass is the probability that the contest
has not finished and nothing has been disclosed. -/
theorem eq_9_belief_law {lam : ℝ} (hlam : 0 < lam) {x0 x1 φ m0 m1 : ℝ → ℝ}
    (hx0 : IsEffort x0) (hx1 : IsEffort x1) (hφ : IsEffort φ)
    (hm0c : ContinuousOn m0 (Set.Ici 0)) (hm1c : ContinuousOn m1 (Set.Ici 0))
    (h00 : 0 < m0 0) (h10 : 0 ≤ m1 0)
    (hm0 : ∀ t, 0 ≤ t → m0 t = m0 0 - ∫ s in (0 : ℝ)..t, lam * x0 s * m0 s)
    (hm1 : ∀ t, 0 ≤ t → m1 t = m1 0 +
      ∫ s in (0 : ℝ)..t, (lam * x0 s * (1 - φ s) * m0 s - lam * x1 s * m1 s)) :
    let p : ℝ → ℝ := fun t => m1 t / (m0 t + m1 t)
    ∀ t, 0 ≤ t → 0 < m0 t + m1 t ∧ p t ∈ Set.Icc (0 : ℝ) 1 ∧
      p t = p 0 + ∫ s in (0 : ℝ)..t,
        (1 - p s) * (x0 s * lam - p s * x1 s * lam - (1 - p s) * x0 s * lam * φ s) := by sorry

end DevContest
