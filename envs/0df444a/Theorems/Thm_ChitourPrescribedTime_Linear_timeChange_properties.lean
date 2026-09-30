-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_timeChange_properties
-- name    : ChitourPrescribedTime.Linear.timeChange_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:58:59.927908+00:00
-- url     : https://prove2.me/theorems/2d883b34-c56a-4df3-9e3f-b23897d2c6a9
-- title:
--   §3 (10) — $\dot\lambda=a\lambda^2$, $\lambda\uparrow\infty$ at $T$, and $s$ is an increasing $C^1$ bijection $[0,T)\to[0,\infty)$
-- statement:
--   Let $T>0$ and let $a:[0,T]\to\mathbb R$ be continuous and nonnegative with $A(t)=\int_t^T a(\xi)\,d\xi>0$ for all $t\in[0,T)$. Put $\lambda(t) = 1/A(t)$ and $s(t)=\int_0^t\lambda(\xi)\,d\xi$ for $0\le t<T$. Then:
--
--   1. $\lambda$ is differentiable on $[0,T)$ (one-sided at $t=0$) with
--   $$\frac{\dot\lambda(t)}{\lambda(t)^2} = a(t), \qquad t\in[0,T);$$
--   2. $\lambda(t)>0$ for $t\in[0,T)$;
--   3. $\lambda$ is nondecreasing on $[0,T)$;
--   4. $\lambda(t)\to+\infty$ as $t\to T^-$;
--   5. $s$ is $C^1$ on $[0,T)$ with $s'(t)=\lambda(t)$ (one-sided at $0$);
--   6. $s$ is strictly increasing on $[0,T)$;
--   7. $s$ maps $[0,T)$ onto $[0,\infty)$.
--
--   These facts make $s$ a legitimate new time: estimates proved on $[0,\infty)$ in the variable $s$ transfer to the prescribed interval $[0,T)$.
--
--   **Formalization Note** The paper says "$\lambda$ is increasing". Since $\dot\lambda = a\lambda^2$ vanishes wherever $a$ does, strict increase is false in general (take $a\equiv 0$ on a subinterval), so item 3 states monotonicity (nondecreasing). Derivatives are taken within $[0,T)$, which gives the right derivative at $t=0$ and the two-sided derivative at interior points.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1027, §3, eq. (10) and the sentence after it

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_timeChange

namespace ChitourPrescribedTime.Linear

/-- §3, p. 1027, (10) and the sentence after it: for an admissible weight `a`, the parameter
`λ = 1/A` satisfies `λ̇ = a λ²` on `[0, T)`, is positive and nondecreasing on `[0, T)` and tends to
`+∞` as `t → T⁻`; the time `s(t) = ∫_0^t λ` is a strictly increasing `C¹` bijection from `[0, T)`
onto `[0, ∞)`. The page's "increasing" for `λ` is read as nondecreasing (`λ̇ = aλ²` vanishes
where `a` does). Derivatives are taken within `[0, T)` (one-sided at `t = 0`). -/
theorem timeChange_properties (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (lam T a) (a t * lam T a t ^ 2) (Set.Ico 0 T) t) ∧
    (∀ t ∈ Set.Ico 0 T, 0 < lam T a t) ∧
    MonotoneOn (lam T a) (Set.Ico 0 T) ∧
    Filter.Tendsto (lam T a) (nhdsWithin T (Set.Iio T)) Filter.atTop ∧
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (sTime T a) (lam T a t) (Set.Ico 0 T) t) ∧
    ContDiffOn ℝ 1 (sTime T a) (Set.Ico 0 T) ∧
    StrictMonoOn (sTime T a) (Set.Ico 0 T) ∧
    sTime T a '' Set.Ico 0 T = Set.Ici 0 := by sorry

end ChitourPrescribedTime.Linear
