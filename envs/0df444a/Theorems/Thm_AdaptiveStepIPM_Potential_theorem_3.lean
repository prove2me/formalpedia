-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Potential_theorem_3
-- name    : AdaptiveStepIPM.Potential.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:02.019617+00:00
-- url     : https://prove2.me/theorems/46cc3b65-1295-4957-b165-b982bd89a497
-- title:
--   Theorem 3 — the potential-reduction Algorithm 3 in $\mathcal N_\infty^-(\beta)$ attains precision $t$ in $\lceil 6nt/(11\beta\gamma(1-\gamma))\rceil$ iterations
-- statement:
--   Consider the standard-form linear program (P) $\min c^Tx$ s.t. $Ax = b$, $x \ge 0$, and its dual (D) $\max b^Ty$ s.t. $A^Ty + s = c$, $s \ge 0$, with $n \ge 1$ variables. Let $\beta, \gamma \in (0,1)$ with $\gamma \le 2(1-\beta)$, let $\mathcal N = \mathcal N_\infty^-(\beta)$, and set
--   $$
--   \rho := n + \Bigl(\frac{3}{\beta\gamma(1-\gamma)}\log\frac{1}{1-\beta}\Bigr) n^2 .
--   $$
--   Let $t > 0$ and let $(x^k, s^k)_{k\ge 0}$ be a run of Algorithm 3 with precision $t$: $(x^0, s^0) \in \mathcal N$, $(x^0)^Ts^0 \le 2^t$, $\psi(x^0, s^0) \le (\rho - n)t + n\log n$, and while $(x^k)^Ts^k > 2^{-t}$ the next iterate is obtained by a step of Algorithm 3 (a direction from (2) with parameter $\gamma$, followed by the step that minimises the potential $\psi$ over all points of the line lying in $\mathcal N$). Then the algorithm terminates in $O(nt)$ iterations; explicitly, there is
--   $$
--   k \le \Bigl\lceil \frac{6nt}{11\beta\gamma(1-\gamma)} \Bigr\rceil \quad\text{with}\quad (x^k)^Ts^k \le 2^{-t}.
--   $$
--
--   Together with Theorem 2 this shows that choosing the step by the potential function, with $\rho - n$ of order $n^2$, gives the same worst-case complexity as the adaptive-step path-following method in the same neighbourhood.
--
--   **Formalization Note** The explicit count comes from the paper's proof: each iteration decreases $\psi$ by at least $11n\log\frac{1}{1-\beta}$, and a total decrease of $2(\rho - n)t$ suffices, since $\psi(x,s) \ge (\rho - n)\log(x^Ts) + n\log n$ and $e^{-t} \le 2^{-t}$; $2(\rho-n)t / (11n\log\frac{1}{1-\beta}) = 6nt/(11\beta\gamma(1-\gamma))$. $\psi$ is the published `LinearOptimization.interiorPointPotential` with parameter $\rho$, evaluated only at strictly positive points. All logarithms are natural, and $2^{\pm t}$ are real powers. The step minimises over every real $\theta$ whose point lies in $\mathcal N$, as printed; a minimiser need not exist, and for $n = 1$ no step exists at all, so for $n = 1$ every run has $(x^0)^Ts^0 \le 2^{-t}$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 11, Theorem 3

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **Theorem 3 (p. 11).** Let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`, `N = N_∞⁻(β)` and
`ρ := n + (3/(βγ(1 − γ)) log(1/(1 − β))) n²`. Then Algorithm 3 terminates in `O(nt)`
iterations; explicitly, every run with precision `t > 0` reaches `(x^k)ᵀs^k ≤ 2^{−t}` for some
`k ≤ ⌈6nt/(11βγ(1 − γ))⌉`. -/
theorem theorem_3 {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (t : ℝ) (ht : 0 < t) (x s : ℕ → Fin n → ℝ)
    (hrun : IsAlg3Run A b c β γ (rho n β γ) t x s) :
    ∃ k : ℕ, k ≤ ⌈6 * (n : ℝ) * t / (11 * β * γ * (1 - γ))⌉₊ ∧
      x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.Potential
