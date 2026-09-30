-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_corollary14_prescribed_time_estimate
-- name    : ChitourPrescribedTime.Linear.corollary14_prescribed_time_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:03:20.215374+00:00
-- url     : https://prove2.me/theorems/eefb7a5d-0a0b-4c9b-bf4c-693338c2e975
-- title:
--   Corollary 14 (corrected) — the feedback $u=-K^TD^{\mathbf r}_{\eta\lambda(t)}x$ drives the perturbed chain of integrators to $0$ at the prescribed time $T$
-- statement:
--   Consider the perturbed chain of integrators
--   $$\dot x(t) = J_n x(t) + \big(d(t) + b(t) u(t)\big) e_n, \qquad t\in[0,T),\ x(t)\in\mathbb R^n,$$
--   with $n\ge 1$ and an uncertain control gain satisfying $b(t)\ge\underline b>0$ (no upper bound). Let $T>0$ and let $a:[0,T]\to\mathbb R$ be continuous and nonnegative with $\int_t^T a(\xi)\,d\xi>0$ for $t\in[0,T)$, and set
--   $$\lambda(t) = \frac{1}{\int_t^T a(\xi)\,d\xi}, \qquad s(t) = \int_0^t \lambda(\xi)\,d\xi, \qquad 0\le t<T.$$
--
--   There are a rate $\mu>0$ and a disturbance gain $C_S>0$, depending only on $n$ and $\underline b$, such that, for every such $T$ and $a$, there exist a gain $K\in\mathbb R^n$ and a constant $C>0$ with the following property. For every $\eta\ge1$, every $b$ with $b\ge\underline b$ on $[0,T)$, every $d$, and every solution $x$ (in integral form) on $[0,T)$ of the closed loop under the state feedback
--   $$u(t) = -K^T D^{\mathbf r}_{\eta\lambda(t)}\, x(t),$$
--   we have, for every $t\in[0,T)$, every $1\le i\le n$ and every $D$ with $|d(r)|\le D$ on $[0,t]$,
--   $$|x_i(t)| \le \frac{1}{(\eta\lambda(t))^{n-i+1}}\Big( C\,\eta\max(1,\eta^{n-1})\, e^{-\mu\eta s(t)}\,\|x(0)\| + C_S\,D \Big).$$
--
--   Since $\lambda(t)\to\infty$ as $t\to T^-$, every coordinate of the state tends to $0$ at the prescribed time $T$, whatever the bounded matched disturbance $d$ and the gain $b\ge\underline b$. The state feedback is linear in $x$ with a time-varying gain.
--
--   **Formalization Note** Estimate (23) as printed is false, and this statement corrects it in three ways. As printed, (23) has no constant in front of the transient term, and its constants $C_S$, $\mu$ depend only on $\underline b$. Counterexample: $n=1$, $a\equiv1$, $T=1/2$ (so $\lambda(0)=2$, $s(0)=0$), $\eta=1$, $d\equiv0$, $x(0)=1$. At $t=0$, (23) reads $1\le\tfrac12$ whatever $K$, $C_S$, $\mu$ are. The corrections: (i) the page's product $C_S\mu$ in the exponent is written as one rate $\mu$, which depends only on $n$ and $\underline b$; (ii) a constant $C$ multiplies the transient term; (iii) $K$ and the transient constant $C$ may depend on $T$ and $a$. The disturbance gain $C_S$ stays as on the page: it depends only on $n$ and $\underline b$ and is quantified before $T$ and $a$. This is what the proof yields: Proposition 12 applied with $\|y(0)\| = \|D^{\mathbf r}_{\lambda(0)}x(0)\|$, and the threshold $\eta_1 = C_a/C_0$ absorbed into $K$. The page's $\max_{r\in[0,t]}|d(t)|$ is read as $\max_{r\in[0,t]}|d(r)|$ and replaced by any bound $D$. The page's "for every $t\ge0$" is restricted to $t\in[0,T)$, where $\lambda$ and $s$ are defined. Solutions are Carathéodory solutions in integral form (`IsIntegralSolution` with integrability on each $[0,t]$). The norm is Euclidean (`eucNorm`). The coordinate `i : Fin n` is the paper's $i=$ `i.val + 1`, so $n-i+1$ is `n - i.val`.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1030, Corollary 14, eqs. (21)–(23) (corrected: constant on the transient term, K and constants allowed to depend on T and a)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Definitions.Def_ChitourPrescribedTime_Linear_timeChange
import Definitions.Def_ChitourPrescribedTime_Linear_closedLoop

namespace ChitourPrescribedTime.Linear

/-- Corollary 14 (p. 1030), **corrected**: estimate (23) for the time-varying feedback (22)
`u = -Kᵀ D^r_{ηλ(t)} x(t)`, with a constant `C` on the transient term and with `K` and `C` allowed
to depend on `T` and `a` (as printed, (23) fails at `t = 0` whenever `∫_0^T a < 1`). The rate `µ`
and the disturbance gain `C_S` depend only on `n` and `b̲`, as on the page. Coordinates: paper index `i.val + 1`, so `n - i + 1 = n - i.val`. -/
theorem corollary14_prescribed_time_estimate (n : ℕ) (hn : 1 ≤ n) (bmin : ℝ) (hbmin : 0 < bmin) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ CS : ℝ, 0 < CS ∧ ∀ (T : ℝ) (a : ℝ → ℝ), AdmissibleWeight T a →
      ∃ K : Fin n → ℝ, ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 1 ≤ η →
        ∀ (b d : ℝ → ℝ) (x : ℝ → Fin n → ℝ),
          (∀ t ∈ Set.Ico 0 T, bmin ≤ b t) →
          IsIntegralSolution (feedbackFieldT n T a b d K η) x (Set.Ico 0 T) →
          ∀ t ∈ Set.Ico 0 T, ∀ i : Fin n, ∀ D : ℝ, (∀ r ∈ Set.Icc 0 t, |d r| ≤ D) →
            |x t i| ≤ 1 / (η * lam T a t) ^ (n - (i : ℕ)) *
              (C * η * max 1 (η ^ (n - 1)) * Real.exp (-(μ * η * sTime T a t)) * eucNorm (x 0) +
                CS * D) := by sorry

end ChitourPrescribedTime.Linear
