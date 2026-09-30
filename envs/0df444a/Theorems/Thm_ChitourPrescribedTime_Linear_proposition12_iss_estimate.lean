-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_proposition12_iss_estimate
-- name    : ChitourPrescribedTime.Linear.proposition12_iss_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:01:52.74174+00:00
-- url     : https://prove2.me/theorems/1692a4c2-bde7-452c-a83b-5bb2413eb2d1
-- title:
--   Proposition 12 (corrected) — ISS estimate (17) for $y'=(aD_{\mathbf r}+J_n)y+(bu+d)e_n$ under $u=-K^TD^{\mathbf r}_\eta y$
-- statement:
--   Let $n\ge 1$ and $\underline b>0$. There exist constants $C_S>0$ and $\rho_1>0$, depending only on $n$ and $\underline b$, with the following property. For every $C_a\ge 0$ there are a gain $K\in\mathbb R^n$ and $\eta_1>0$ such that, for every $\eta\ge\eta_1$:
--
--   - let $a, b, d:[0,\infty)\to\mathbb R$ satisfy $|a(s)|\le C_a$ and $b(s)\ge\underline b$ for all $s\ge 0$;
--   - let $y:[0,\infty)\to\mathbb R^n$ be a solution (in integral form) of
--   $$y' = \big(a(s) D_{\mathbf r} + J_n\big) y + \big(b(s) u(s) + d(s)\big) e_n, \qquad u = -K^T D^{\mathbf r}_\eta\, y .$$
--
--   Then for every $s\ge 0$, every $1\le i\le n$ and every $D$ with $|d(r)|\le D$ for all $r\in[0,s]$,
--   $$|y_i(s)| \le C_S\,\frac{\max(1,\eta^{n-1})}{\eta^{n-i}}\, e^{-C_S\rho_1\eta s}\,\|y(0)\| + \frac{C_S}{\eta^{n-i+1}}\, D .$$
--
--   This is an input-to-state stability estimate for the transformed system, with an exponential rate proportional to the feedback parameter $\eta$. Transported back to the original time by the change of variables $y = D^{\mathbf r}_{\lambda(t)}x$, it yields the prescribed-time estimate of Corollary 14.
--
--   **Formalization Note** As printed, estimate (17) has no constant in front of the transient term, and it is false for $n\ge 2$. Take $a\equiv 1$, $b\equiv\underline b$, $d\equiv 0$, $y(0)=e_1$. The first row of the closed loop is $y_1' = n a\, y_1 + y_2$, so $y_1'(0) = n > 0$ and $|y_1(s)|>1$ for small $s>0$. The printed bound at $i=1$ is $e^{-C_S\rho_1\eta s}<1$. The statement here puts the factor $C_S$ on the transient term; this is what the paper's Lyapunov argument gives, once the condition number of $S$ is kept. The constants $C_S$, $\rho_1$ depend only on $\underline b$ (and $n$), as the page says; $K$ and $\eta_1$ are chosen after the dynamics, as in the page's "there exists $K$ … and $\eta_1$", and depend on $a$ only through $C_a=\sup|a|$. The statement holds for every $a$ bounded by $C_a$, not only for the specific $a(s)$ produced by the time change. The Euclidean norm is `eucNorm`. The coordinate `i : Fin n` is the paper's $i=$ `i.val + 1`, so $n-i$ is `n - 1 - i.val` and $n-i+1$ is `n - i.val`. The bound $D$ replaces $\max_{r\in[0,s]}|d(r)|$, which avoids a supremum of a possibly unbounded function.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), pp. 1028–1029, Proposition 12, eq. (17) (corrected: constant C_S on the transient term)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Definitions.Def_ChitourPrescribedTime_Linear_timeChange
import Definitions.Def_ChitourPrescribedTime_Linear_closedLoop

namespace ChitourPrescribedTime.Linear

/-- Proposition 12 (pp. 1028–1029), **corrected**: estimate (17) with the constant `C_S` also on the
transient term (as printed, (17) fails for `n ≥ 2`; see the natural-language statement). There are
`C_S, ρ₁ > 0`, depending only on `n` and `b̲`, such that for every bound `C_a ≥ 0` of `|a|`
there are `K ∈ ℝ^n` and `η₁ > 0` (the page's "there exists K … and η₁", after the dynamics) such that
for every `η ≥ η₁`, every `a, b, d` with `|a| ≤ C_a` and `b ≥ b̲` on `[0, ∞)`, every solution `y` of (11) closed by `u = -Kᵀ D^r_η y` (i.e. (13)) on `[0, ∞)`, every
`s ≥ 0`, every coordinate `i` (paper index `i.val + 1`) and every bound `D` of `|d|` on `[0, s]`:
`|y_i(s)| ≤ C_S max(1, η^{n-1}) / η^{n-i} · exp(-C_S ρ₁ η s) ‖y(0)‖ + C_S / η^{n-i+1} · D`. -/
theorem proposition12_iss_estimate (n : ℕ) (hn : 1 ≤ n) (bmin : ℝ) (hbmin : 0 < bmin) :
    ∃ CS : ℝ, 0 < CS ∧ ∃ ρ1 : ℝ, 0 < ρ1 ∧
      ∀ Ca : ℝ, 0 ≤ Ca → ∃ K : Fin n → ℝ, ∃ η1 : ℝ, 0 < η1 ∧ ∀ η : ℝ, η1 ≤ η →
        ∀ (a b d : ℝ → ℝ) (y : ℝ → Fin n → ℝ),
          (∀ s, 0 ≤ s → |a s| ≤ Ca) →
          (∀ s, 0 ≤ s → bmin ≤ b s) →
          IsIntegralSolution (feedbackFieldS n a b d K η) y (Set.Ici 0) →
          ∀ s : ℝ, 0 ≤ s → ∀ i : Fin n, ∀ D : ℝ, (∀ r ∈ Set.Icc 0 s, |d r| ≤ D) →
            |y s i| ≤ CS * (max 1 (η ^ (n - 1)) / η ^ (n - 1 - (i : ℕ))) *
                  Real.exp (-(CS * ρ1 * η * s)) * eucNorm (y 0) +
                CS / η ^ (n - (i : ℕ)) * D := by sorry

end ChitourPrescribedTime.Linear
