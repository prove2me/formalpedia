-- Prove2me | Theorems.Thm_ErlangA_Diffusion_theorem_2
-- name    : ErlangA.Diffusion.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:12.512033+00:00
-- url     : https://prove2.me/theorems/b4aeb349-7de2-4e4d-9df8-f63572aff4ab
-- title:
--   Theorem 2 — in the Halfin–Whitt regime the scaled Erlang-A queue $q_N$ converges weakly to the diffusion $dq = f(q)\,dt + \sqrt{2\mu}\,db$
-- statement:
--   For $N \ge 1$, consider the Erlang-A ($M/M/N+M$) queue with $N$ agents, Poisson arrivals of rate $\lambda_N > 0$, exponential service of rate $\mu > 0$ per agent (the same for all $N$) and exponential patience of rate $\theta_N > 0$. Let $Q_N(t)$ be its number of callers at time $t$, with an arbitrary initial value $Q_N(0)$, and let
--   $$
--   q_N(t) = \frac{Q_N(t) - N}{\sqrt N}, \qquad \rho_N = \frac{\lambda_N}{N\mu}.
--   $$
--   Assume
--   $$
--   \lim_{N\to\infty}\sqrt N(1 - \rho_N) = \beta,\quad -\infty < \beta < \infty, \qquad \lim_{N\to\infty}\theta_N = \theta,\quad 0 < \theta < \infty,
--   $$
--   and that $q_N(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$. Then
--
--   1. $q_N \Rightarrow q$ (weak convergence of processes), where $q$ solves
--   $$
--   dq(t) = f(q)\,dt + \sqrt{2\mu}\,db(t),\qquad f(x) = \begin{cases} -\mu(\beta + x), & x \le 0,\\ -(\mu\beta + \theta x), & x > 0,\end{cases}
--   $$
--   with $b$ a standard Brownian motion and $q(0) \sim \nu$ independent of $b$;
--   2. this solution is unique: any two solutions with initial law $\nu$ have the same law on path space.
--
--   In words: when staffing follows $N \approx R + \beta\sqrt R$ with offered load $R = \lambda_N/\mu$ and patience rates converge, the queue length fluctuates around $N$ on the scale $\sqrt N$ like a diffusion that is an Ornstein–Uhlenbeck process with restraining force $\mu$ below $N$ and $\theta$ above. This is the basis of the paper's QED approximations $Q_N \approx N + q\sqrt N$.
--
--   **Formalization Note** All the systems live on one probability space; this is no loss, since weak convergence depends only on the laws. $Q_N$ is realized through the Poisson time-change representation (`ErlangA.Diffusion.Queue`). The hypothesis $q_N(0) \Rightarrow \nu$ is stated as convergence of $E[g(q_N(0))]$ to $\int g\,d\nu$ for every bounded continuous $g$. Process-level weak convergence $q_N \Rightarrow q$ in $D[0,\infty)$ is stated in the coupling form `BellWilliams2001.ThresholdPolicy.CouplingConverges` (Skorokhod representation with almost-sure uniform convergence on compact time intervals), which is equivalent because the limit has continuous paths. The limit lives on a probability space in universe `Type`.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 216, Theorem 2

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ErlangA.Diffusion

open BellWilliams2001.ThresholdPolicy

/-- **Theorem 2** (p. 216). Let `μ > 0`, `β ∈ ℝ`, `θ ∈ (0, ∞)`, and for `N ≥ 1` let `Q_N` be
the queue-length process of an Erlang-A system with `N` agents, arrival rate `λ_N > 0`, service
rate `μ` and patience rate `θ_N > 0`, all systems on one probability space. Assume
`√N (1 − ρ_N) → β` with `ρ_N = λ_N/(Nμ)`, `θ_N → θ`, and that `q_N(0) = (Q_N(0) − N)/√N`
converges in distribution to a probability law `ν` on `ℝ`. Then:
1. there is a solution `q` of `dq(t) = f(q) dt + √(2μ) db(t)` with `q(0) ∼ ν` independent of
   the standard Brownian motion `b`, and `q_N ⇒ q` (weak convergence in `D[0, ∞)`, in the
   coupling form `CouplingConverges`);
2. the solution is unique in law: any two solutions with initial law `ν` have the same law on
   path space. -/
theorem theorem_2 (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (lam thetaN : ℕ → ℝ) (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N)
    (hthetaN : ∀ N : ℕ, 1 ≤ N → 0 < thetaN N)
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - trafficIntensity lam μ N)) atTop (𝓝 β))
    (hθN : Tendsto thetaN atTop (𝓝 θ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S R : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ N : ℕ, 1 ≤ N →
      IsErlangASystem P N (lam N) μ (thetaN N) (A N) (S N) (R N) (Q N))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ ω, g (scaled N (Q N) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (b : ℝ≥0 → Ω' → ℝ)
        (q : Ω' → ℝ → ℝ),
        IsDiffusionSolution P' μ β θ (ν : Measure ℝ) b q ∧
        CouplingConverges P P' (fun N => scaled N (Q N)) (fun ω t (_ : Fin 1) => q ω t)) ∧
    ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) (b₁ : ℝ≥0 → Ω₁ → ℝ)
      (q₁ : Ω₁ → ℝ → ℝ) (Ω₂ : Type) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
      (b₂ : ℝ≥0 → Ω₂ → ℝ) (q₂ : Ω₂ → ℝ → ℝ),
      IsDiffusionSolution P₁ μ β θ (ν : Measure ℝ) b₁ q₁ →
      IsDiffusionSolution P₂ μ β θ (ν : Measure ℝ) b₂ q₂ →
      IdentDistrib (fun ω (t : ℝ≥0) => q₁ ω t) (fun ω (t : ℝ≥0) => q₂ ω t) P₁ P₂ := by sorry

end ErlangA.Diffusion
