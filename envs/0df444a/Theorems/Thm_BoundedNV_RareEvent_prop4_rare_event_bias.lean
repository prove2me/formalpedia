-- Prove2me | Theorems.Thm_BoundedNV_RareEvent_prop4_rare_event_bias
-- name    : BoundedNV.RareEvent.prop4_rare_event_bias
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:02:01.460993+00:00
-- url     : https://prove2.me/theorems/2db8c826-4c72-4178-8732-73c2aef65896
-- title:
--   Proposition 4, p. 577 — rare-event bias with an optimal midpoint
-- statement:
--   Let nonnegative demand have density $f$ supported on $[a,b]$, with $0\le a<b$, and set $m=(a+b)/2$. A newsvendor sells at price $p$ and pays unit cost $c$, where $0<c<p$. Assume $m$ maximizes the expected profit $\pi(x)=p\mathbb E[\min(D,x)]-cx$ over all real orders. Let the behavioral order $X^\flat$ have logit density proportional to $e^{\pi(x)/\beta}$ on $[a,b]$, where $\beta>0$. Then
--
--   $$
--   \begin{aligned}
--   f\text{ strictly decreasing on }[a,b]&\implies \mathbb E[X^\flat]>m,\\
--   f\text{ strictly increasing on }[a,b]&\implies \mathbb E[X^\flat]<m.
--   \end{aligned}
--   $$
--
--   Thus the behavioral expected order is pulled toward the low-probability end of the demand interval when the rational optimum is at its midpoint.
--
--   **Formalization Note** Strict monotonicity is necessary for strict inequalities; constant demand density with midpoint optimum gives equality. The paper's prose reverses the labels of overordering and underordering, while its proof has the inequality above. The interval $[a,b]$ is the decision domain. The normalizer is positive because profit is continuous on this nondegenerate compact interval.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 577 (PDF 12), Proposition 4; proof pp. 586–587 (PDF 21–22)

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

namespace BoundedNV.RareEvent

/-- Proposition 4, p. 577, with the strict monotonicity used in its proof. -/
theorem prop4_rare_event_bias (f : ℝ → ℝ) (p c β a b : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ x ∉ Set.Icc a b, f x = 0)
    (hp : 0 < c) (hpc : c < p) (hβ : 0 < β)
    (hm : IsMaxOn (BoundedNV.Uniform.nvProfit f p c) Set.univ ((a + b) / 2)) :
    (StrictAntiOn f (Set.Icc a b) →
      (a + b) / 2 < BoundedNV.Uniform.logitExp (Set.Icc a b) (BoundedNV.Uniform.nvProfit f p c) β id) ∧
    (StrictMonoOn f (Set.Icc a b) →
      BoundedNV.Uniform.logitExp (Set.Icc a b) (BoundedNV.Uniform.nvProfit f p c) β id < (a + b) / 2) := by sorry

end BoundedNV.RareEvent
