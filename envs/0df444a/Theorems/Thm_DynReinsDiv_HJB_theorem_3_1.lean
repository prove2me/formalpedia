-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_theorem_3_1
-- name    : DynReinsDiv.HJB.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:19.924776+00:00
-- url     : https://prove2.me/theorems/b559229e-7694-44e5-a96d-4c1b86aac24a
-- title:
--   Theorem 3.1 — the HJB variational inequality (3.1) has a unique classical solution satisfying (3.4)–(3.9)
-- statement:
--   Fix a model: a nonnegative claim law with distribution function $F$ satisfying the tail assumption (3.3), loadings with $0<\gamma<\mu_1$, discount factor $c>0$ and horizon $T>0$. Let $\mathcal Q_T=(0,\infty)\times(0,T]$ and $\overline{\mathcal Q}_T=[0,\infty)\times[0,T]$, and let $\lambda$ be the positive root of $f(y)=-yA(y)+B(y)-\gamma$ (A.12).
--
--   The variational inequality
--   $$\min\{v_t-\mathcal Lv,\ v_x-1\}=0\ \text{in }\mathcal Q_T,\qquad v(0,t)=0\ (0<t\le T),\qquad v(x,0)=x\ (x>0), \tag{3.1}$$
--   with $\mathcal L$ the operator (3.2), has a solution $v\in C^{2,1}(\overline{\mathcal Q}_T\setminus\{(0,0)\})\cap C(\overline{\mathcal Q}_T)$ that satisfies, in $\mathcal Q_T$,
--   1. $v_x\ge1$ (3.4);
--   2. $v_t\ge0$ (3.5);
--   3. $v_{xx}\le0$ (3.6);
--   4. $v_{xxx}\ge0$ in the weak sense (3.7);
--   5. $v_{xt}\ge0$ (3.8);
--   6. $\lambda v_x+v_{xx}\ge0$ (3.9).
--
--   Any other solution of (3.1) in the same class with properties (3.4)–(3.9) coincides with $v$ on $\overline{\mathcal Q}_T$.
--
--   The solution is the candidate value function of the finite-horizon problem of maximising expected discounted dividends with dynamic reinsurance (with $t$ the time to maturity); Theorem 3.2 of the paper identifies it with the value function, and its concavity and the bound (3.9) underlie the description of the optimal reinsurance and dividend strategies in Section 4.
--
--   **Formalization Note** The derivatives $v_x, v_{xx}, v_t$ are explicit functions, equal to the partial derivatives at interior points and extended continuously to $\overline{\mathcal Q}_T\setminus\{(0,0)\}$; (3.1) is imposed at $t=T$ through these extensions. (3.7) is read as: $x\mapsto v_{xx}(x,t)$ nondecreasing on $(0,\infty)$ for each $t\in(0,T]$; (3.8) as: $t\mapsto v_x(x,t)$ nondecreasing on $(0,T]$ for each $x>0$. (3.9) is imposed for every positive root of $f$; there is exactly one (milestone (A.13)). Uniqueness is within the class of solutions with (3.4)–(3.9) and means equality on $\overline{\mathcal Q}_T$; values outside $\overline{\mathcal Q}_T$ are unconstrained.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 9, Theorem 3.1 (with (3.1)–(3.3), p. 8–9, and (A.12), p. 23)

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem theorem_3_1 (M : Model) :
    ∃ v vx vxx vt : ℝ → ℝ → ℝ,
      IsC21 M.T v vx vxx vt ∧ SolvesVI M v vx vxx vt ∧ HJBProps M v vx vxx vt ∧
      ∀ w wx wxx wt : ℝ → ℝ → ℝ,
        IsC21 M.T w wx wxx wt → SolvesVI M w wx wxx wt → HJBProps M w wx wxx wt →
          Set.EqOn (Function.uncurry w) (Function.uncurry v) (QTbar M.T) := by sorry

end DynReinsDiv.HJB
