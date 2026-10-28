-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_eq_A9_solves_A8
-- name    : DynMomentum.ShortHorizon.eq_A9_solves_A8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:30.773986+00:00
-- url     : https://prove2.me/theorems/2bdfdee1-0ac4-4d03-851e-9f1d73cdb1cf
-- title:
--   (A.9), Appendix A.2, p. 27 — the exponential-quadratic ansatz solves the Feynman–Kac PDE (A.8) when (A₁, A₂, A₃) solve (A.9)
-- statement:
--   Let the parameters $(\alpha,\sigma,\tau,\gamma,r,\mu)$ satisfy $0<\alpha<1$, $\sigma,\tau,\gamma>0$, let $0\le T\le\tau$, and let $s$ be a log-price path continuous on $[-\tau,0]$. Suppose $(A_1,A_2,A_3)$ solve the ODE system (A.9) on $[0,T]$ with $A_{1,T}=A_{2,T}=A_{3,T}=0$, the forcing at time $t$ being the realized past log price $s_{t-\tau}$. Put
--   $$f(x,t) = \exp\{A_{1,t}x^2/2 + A_{2,t}x + A_{3,t}\}.$$
--   Then for every $t\in[0,T]$ and every $x\in\mathbb R$, $f$ satisfies the Feynman–Kac equation (A.8),
--   $$\frac{\partial f}{\partial t} + \Big[\Big(r-\frac{\sigma^2}2\Big)\Big(1-\frac\alpha\gamma\Big)+(1-\alpha)\frac\mu\gamma+\frac{\alpha}{\gamma\tau}(x-s_{t-\tau})\Big]\frac{\partial f}{\partial x} + \frac{\sigma^2}2\frac{\partial^2 f}{\partial x^2} + \frac{1-\gamma}{2\gamma^2\sigma^2}\Big[(1-\alpha)\mu-\alpha\Big(r-\frac{\sigma^2}2\Big)+\frac\alpha\tau(x-s_{t-\tau})\Big]^2 f = 0,$$
--   and $f(x,T)=1$ for all $x$.
--
--   This is the deterministic content of the sentence "Its solution is given by" in the proof of Proposition 3.3: it reduces the PDE for the conditional expectation (A.7) to the ODE system (A.9).
--
--   **Formalization Note.** The time derivative is a derivative within $[0,T]$ (one-sided at the endpoints); at $T=0$ the first clause is a statement about one point. The space derivatives are Mathlib's `deriv` of the smooth function $x\mapsto f(x,t)$. The PDE variable is named $x$ because $s$ denotes the path. The hypothesis $T\le\tau$ is §3.1's setting, under which $s_{t-\tau}$ is already realized.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 27 (PDF 27), (A.8)–(A.9), proof of Proposition 3.3, Appendix A.2

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- (A.9), proof of Proposition 3.3 (Li & Liu 2022, p. 27): if `(A₁, A₂, A₃)` solve (A.9) on
`[0, T]` with zero terminal values, the ansatz `f(x, t) = exp{A₁,ₜ x²/2 + A₂,ₜ x + A₃,ₜ}` solves the
Feynman–Kac PDE (A.8) on `[0, T]` (time derivative taken within `[0, T]`), and `f(x, T) = 1`. -/
theorem eq_A9_solves_A8 (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0)) (A1 A2 A3 : ℝ → ℝ)
    (hA : SolvesA9Full P T s A1 A2 A3) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      HasDerivWithinAt (fun t' => ansatz A1 A2 A3 x t')
        (-(pdeDrift P s t x * deriv (fun y => ansatz A1 A2 A3 y t) x
            + P.σ ^ 2 / 2 * deriv (deriv (fun y => ansatz A1 A2 A3 y t)) x
            + pdePotential P s t x * ansatz A1 A2 A3 x t))
        (Set.Icc 0 T) t) ∧
    ∀ x : ℝ, ansatz A1 A2 A3 x T = 1 := by sorry

end DynMomentum.ShortHorizon
