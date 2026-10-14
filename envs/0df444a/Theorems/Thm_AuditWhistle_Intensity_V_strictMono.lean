-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_V_strictMono
-- name    : AuditWhistle.Intensity.V_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:19.236367+00:00
-- url     : https://prove2.me/theorems/092a481c-ae1c-49d0-b3c8-0a280244dea6
-- title:
--   Appendix, proof of Proposition 2, (28), pp. 32–33 — the gap function V characterizes the equilibrium and is strictly increasing in a*
-- statement:
--   Fix a model and $\tau\in(0,1)$, and let $V(a)=a-(1-p)d\,[\beta\tau e_1(a)+(1-\beta\tau)e_0(a,\tau)]$ be the gap function (28), with $r=R/\gamma$, $d=D/k$ and $e_1,e_0$ the reaction functions (25)–(26). Then:
--
--   1. for $a\in(0,1)$, there are $e_1,e_0$ with $(a,e_1,e_0)$ an equilibrium if and only if $V(a)=0$;
--   2. $V$ is strictly increasing on $[0,1]$ (the paper's $\partial V(a^*)/\partial a^*>0$);
--   3. $V(0)<0$ and $V(1)=1$.
--
--   Together these say that the equilibrium audit quality is the unique root of $V$ in $(0,1)$, and that $da^*/d\tau$ has the sign of $-\partial V/\partial\tau$.
--
--   **Formalization Note** The positivity of $\partial V/\partial a^*$ is formalized as strict monotonicity, because $V$ has a kink at the point where $e_1$ reaches $1$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), pp. 32–33, Appendix, proof of Proposition 2, (28)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
import Definitions.Def_AuditWhistle_Intensity_Reaction

namespace AuditWhistle.Intensity

theorem V_strictMono (M : Model) (τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    (∀ a ∈ Set.Ioo (0:ℝ) 1, (∃ e1 e0 : ℝ, IsEquilibrium M τ a e1 e0) ↔ V M τ a = 0) ∧
    StrictMonoOn (V M τ) (Set.Icc (0:ℝ) 1) ∧ V M τ 0 < 0 ∧ V M τ 1 = 1 := by sorry

end AuditWhistle.Intensity
