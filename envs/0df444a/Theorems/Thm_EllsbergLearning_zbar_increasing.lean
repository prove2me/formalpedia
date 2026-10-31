-- Prove2me | Theorems.Thm_EllsbergLearning_zbar_increasing
-- name    : EllsbergLearning.zbar_increasing
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:31.904957+00:00
-- url     : https://prove2.me/theorems/f6fa5ac8-b2f8-44fb-b8e8-d82ed6a628f4
-- title:
--   §5.3, p.32 — $\overline z$ is increasing in $\epsilon$
-- statement:
--   Let $0<\alpha<\tfrac12$, $\sigma>0$, $c>0$, and let $\hat r\in(0,1)$ solve $l(\hat r)=2\alpha^3/(c\sigma^2)$ (22). If $0<\epsilon<\epsilon'<2\hat r-1$ and $\bar r,\bar r'\in(0,1)$ solve (24) for $\epsilon$ and $\epsilon'$ respectively, then
--   $$\overline z(\epsilon,\bar r)=\frac{\sigma^2}{2\alpha}\Big[\log\frac{1+\epsilon}{1-\epsilon}+\log\frac{\bar r}{1-\bar r}\Big]<\overline z(\epsilon',\bar r').$$
--
--   The continuation interval $(-\overline z,\overline z)$ widens with ambiguity: more ambiguity means longer sampling, as long as some learning is optimal.
--
--   Differences from the source:
--   - reading: "$\overline z$ is increasing in $\epsilon$: $d\overline z/d\epsilon>0$" → strictly increasing on $(0,2\hat r-1)$, comparing $\overline z(\epsilon,\bar r)$ and $\overline z(\epsilon',\bar r')$ with $\bar r,\bar r'$ the roots of (24); reason: $\bar r$ is a function of $\epsilon$ through (24); a positive derivative gives strict monotonicity
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §5.3, p.32

import Definitions.Def_EllsbergLearning_CriticalValues
import Definitions.Def_EllsbergLearning_Ellsberg

open Set

namespace EllsbergLearning

/-- `z̄` is increasing in `ϵ` (Epstein & Ji, arXiv:1708.01890v2, §5.3, p.32: "Finally, we show
that z̄ is increasing in ϵ"). For `0 < α < 1/2`, `σ > 0`, `c > 0` and `r̂ ∈ (0, 1)` with
`l(r̂) = 2α³/(cσ²)`: if `0 < ϵ < ϵ' < 2r̂ − 1` and `r̄, r̄' ∈ (0, 1)` solve (24) for `ϵ` and `ϵ'`
respectively, then `z̄(ϵ, r̄) < z̄(ϵ', r̄')`, with `z̄` of (23).

**Formalization Note.** The page derives `dz̄/dϵ > 0`; the statement is the strict monotonicity on
`(0, 2r̂ − 1)` that this gives. -/
theorem zbar_increasing (α σ c : ℝ) (hα : 0 < α) (hα' : α < 1 / 2) (hσ : 0 < σ) (hc : 0 < c)
    (rhat : ℝ) (hrhat : rhat ∈ Ioo (0 : ℝ) 1) (hl : ell rhat = 2 * α ^ 3 / (c * σ ^ 2))
    (ϵ ϵ' rbar rbar' : ℝ) (hϵ : 0 < ϵ) (hϵϵ' : ϵ < ϵ') (hϵ' : ϵ' < 2 * rhat - 1)
    (hrbar : rbar ∈ Ioo (0 : ℝ) 1) (h24 : ell rbar + ell ((1 + ϵ) / 2) = 4 * α ^ 3 / (c * σ ^ 2))
    (hrbar' : rbar' ∈ Ioo (0 : ℝ) 1)
    (h24' : ell rbar' + ell ((1 + ϵ') / 2) = 4 * α ^ 3 / (c * σ ^ 2)) :
    zbar α ϵ σ rbar < zbar α ϵ' σ rbar' := by sorry

end EllsbergLearning
