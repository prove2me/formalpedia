-- Prove2me | Theorems.Thm_AugLagLLC_Penalty_theorem_5_4
-- name    : AugLagLLC.Penalty.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:37.945496+00:00
-- url     : https://prove2.me/theorems/3fe5a505-2853-4473-9957-3c19a0f551b4
-- title:
--   Theorem 5.4, pp. 12–13 — for equality-constrained problems under Assumptions 1–6 and εₖ ≤ ηₖ‖h₁(xₖ)‖∞, ηₖ → 0, the penalty parameters {ρₖ} are bounded
-- statement:
--   Consider the equality-constrained problem
--   $$\text{Minimize } f(x)\ \text{ subject to } h_1(x)=0,\ h_2(x)=0, \tag{5.1}$$
--   with $f,h_1,h_2$ continuously differentiable, where $h_1$ are the upper-level constraints handled by the augmented Lagrangian and $h_2$ the lower-level ones kept in the subproblems. Run Algorithm 3.1 with parameters $\tau\in(0,1)$, $\gamma>1$, $\rho_1>0$, a safeguard box $[\bar\lambda_{\min},\bar\lambda_{\max}]$ and tolerances $\varepsilon_k\to0$, where $\bar\lambda_{k+1}$ is the projection of $\lambda_{k+1}=\bar\lambda_k+\rho_kh_1(x_k)$ on the box. Suppose:
--
--   1. (Assumption 1) $x_k\to x_*$;
--   2. (Assumption 2) $h_1(x_*)=0$, $h_2(x_*)=0$;
--   3. (Assumption 3) $\nabla[h_1(x_*)]_1,\dots,\nabla[h_1(x_*)]_{m_1},\nabla[h_2(x_*)]_1,\dots,\nabla[h_2(x_*)]_{m_2}$ are linearly independent;
--   4. (Assumption 4) $f,h_1,h_2$ have continuous second derivatives in a neighbourhood of $x_*$;
--   5. (Assumption 5) the second-order sufficient condition holds at $x_*$ with Lagrange multipliers $\lambda_*,v_*$;
--   6. (Assumption 6) $[\lambda_*]_i\in([\bar\lambda_{\min}]_i,[\bar\lambda_{\max}]_i)$ for all $i$;
--   7. there is a sequence $\eta_k\to0$ with $\varepsilon_k\le\eta_k\|h_1(x_k)\|_\infty$ for every outer iteration $k$.
--
--   Then the sequence of penalty parameters $\{\rho_k\}$ is bounded.
--
--   The theorem says that when the safeguard box contains the true multipliers and the subproblems are solved with a precision proportional to the current infeasibility, the augmented Lagrangian method does not degenerate into an external penalty method with ill-conditioned subproblems.
--
--   **Formalization Note** The page allows $\tau\in[0,1)$; the hypothesis $\tau>0$ is added because the statement is false for $\tau=0$. Example: $f(x)=x^2$, $h_1(x)=x-1$, no $h_2$, a box containing $\lambda_*=-2$ in its interior, $\bar\lambda_1=0$ and exact subproblem solutions ($\varepsilon_k=0$); then $h_1(x_k)=-(\bar\lambda_k+2)/(2+\rho_k)\ne0$ for every $k$, the test "$\le0$" of Step 4 fails at every iteration, and $\rho_k=\gamma^{k-1}\rho_1\to\infty$ while Assumptions 1–6 hold. The proof's last step needs $3LM^2/\rho_k\le\tau$. "For all $k\in\mathbb N$" in the tolerance hypothesis is read over the outer iterations $k\ge1$. Assumption 5 is pinned to Fletcher's equality-constrained second-order condition (see the SecondOrder definition). Problem (5.1) is (2.1) with $p_1=p_2=0$; the inequality data live on `Fin 0`, so $\|\sigma_k\|_\infty=0$ and Step 4 tests $\|h_1(x_k)\|_\infty$ alone.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 12–13, Theorem 5.4 (with Assumptions 1–6 and the Definition of §5.1, p. 11)

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_SecondOrder

open Filter
open scoped Topology

namespace AugLagLLC.Penalty

/-- Theorem 5.4, pp. 12–13: if Assumptions 1–6 hold for a run of Algorithm 3.1 on the
equality-constrained problem (5.1), and `εₖ ≤ ηₖ ‖h₁(xₖ)‖∞` for every outer iteration `k ≥ 1`
with `ηₖ → 0`, then the penalty parameters `{ρₖ}` are bounded. The hypothesis `0 < τ` is added
to the page's `τ ∈ [0, 1)`: with `τ = 0` the statement is false. -/
theorem theorem_5_4
    {n m1 m2 : ℕ} (P : Problem n m1 0 m2 0) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin 0 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin 0 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin 0 → ℝ}
    -- Assumption 1: a run of Algorithm 3.1 on (5.1), with the safeguard Definition of §5.1
    (hrun : P.IsProjRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : Tendsto x atTop (𝓝 xs))
    -- Assumption 2
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    -- Assumption 3
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i => gradient (P.h1 i) xs) (fun i => gradient (P.h2 i) xs)))
    -- Assumption 4
    (hC2 : P.IsC2At xs)
    -- Assumption 5
    (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ) (hSOSC : P.SOSC0 lamS vS xs)
    -- Assumption 6
    (hbox : ∀ i, lamMin i < lamS i ∧ lamS i < lamMax i)
    -- added: `τ > 0`
    (hτ : 0 < τ)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hεη : ∀ k, 1 ≤ k → ε k ≤ η k * ‖P.h1vec (x k)‖)
    :
    BddAbove (Set.range ρ) := by sorry

end AugLagLLC.Penalty
