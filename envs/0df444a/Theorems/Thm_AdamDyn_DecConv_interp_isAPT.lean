-- Prove2me | Theorems.Thm_AdamDyn_DecConv_interp_isAPT
-- name    : AdamDyn.DecConv.interp_isAPT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:09.9354+00:00
-- url     : https://prove2.me/theorems/cbfc66d5-ddbf-47bd-b545-9d9c9105f938
-- title:
--   §9.1 — the interpolated Adam process is a.s. a bounded asymptotic pseudotrajectory of the (ODE$_\infty$) semiflow
-- statement:
--   Let $(\Omega, \mathcal F, \mathbb P)$ be a probability space, $\xi$ a random variable with law $\mu$ on $\Xi$, $f$ an integrand with gradient $\nabla f$, and $F$, $S$, $\mathcal S$ as in (2.2). Let $\varepsilon > 0$ and let $(\gamma_n, \alpha_n, \beta_n)$ satisfy Assumption 5.1 with constants $0 < b < 4a$, with moreover $\alpha_1 < 1$ and $\beta_1 < 1$. Assume Assumption 2.2, Assumption 2.3 ($F$ coercive), Assumption 2.4 ($S(x) > 0$ coordinatewise for all $x$), Assumption 4.1 (the samples $\xi_1, \xi_2, \dots$ are iid with law $\mu$) and Assumption 4.2 i) with $p = 4$. Let $z_n = (x_n, m_n, v_n)$ be the iterates of Algorithm 5.1 from $(x_0, 0, 0)$, and assume that, with probability one, the sequence $(z_n)$ is bounded.
--
--   Let $\Phi$ be the semiflow (7.8) of $(\mathrm{ODE}_\infty)$ on $\mathcal Z_+$ (with the field $h_\infty$ built from $a$, $b$, $\varepsilon$ and the $F$, $S$ of (2.2)). Let $\bar z_n = (x_{n-1}, m_n, v_n)$, $\tau_n = \sum_{k=0}^n \gamma_k$, and let $\bar z : [0,+\infty) \to \mathcal Z_+$ be the interpolated process
--   $$ \bar z(t) = \bar z_n + (t - \tau_n)\frac{\bar z_{n+1} - \bar z_n}{\gamma_{n+1}} \qquad (t \in [\tau_n, \tau_{n+1}),\ n \in \mathbb N). $$
--   Then, almost surely, $\bar z$ is a bounded **asymptotic pseudotrajectory** of $\Phi$: $\bar z$ is continuous, bounded, and for every $T > 0$
--   $$ \lim_{t \to +\infty} \sup_{s \in [0, T]} d\big(\bar z(t + s), \Phi_s(\bar z(t))\big) = 0 . $$
--
--   This is the step where the stochastic approximation method enters (the paper invokes "usual stochastic approximation arguments" of Benaïm): it transfers the asymptotic behaviour of $(\mathrm{ODE}_\infty)$ to the iterates.
--
--   **Formalization Note** The hypotheses are those of Theorem 5.2 except the empty-interior condition on $F(\mathcal S)$, which this step does not use. The asymptotic pseudotrajectory is the published definition `StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory` (time in $\mathbb R_{\ge 0}$). $\bar z$ takes values in $\mathcal Z_+$ because $v_n \ge 0$; it is passed to the subtype through $(x, m, v) \mapsto (x, m, |v|)$, the identity on $\mathcal Z_+$. On $[0, \tau_0)$, which the page does not cover, $\bar z = \bar z_0 = (x_0, 0, 0)$; this does not affect the asymptotic statement. The semiflow $\Phi$ is a parameter assumed to be the (unique) semiflow of $(\mathrm{ODE}_\infty)$; its existence is Proposition 7.13.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 26, §9.1 (proof of Theorem 5.2): "the interpolated process z̄ … is almost surely a bounded APT of the semiflow Φ̄ defined by (ODE∞)"

import Mathlib
import Definitions.Def_AdamDyn_DecConv_ODEInf
import Definitions.Def_AdamDyn_DecConv_Algorithm
import Definitions.Def_AdamDyn_DecConv_StochasticModel
import Definitions.Def_AdamDyn_DecConv_ProofQuantities
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory

open MeasureTheory Filter Topology
open scoped NNReal

namespace AdamDyn.DecConv

/-- §9.1, proof of Theorem 5.2 (Barakat & Bianchi, arXiv:1810.02263v4, p. 26): under the
hypotheses of Theorem 5.2 (except the empty-interior condition on `F(𝒮)`, which this step does
not use), with `F`, `S` those of (2.2), let `Φ` be the semiflow of `(ODE∞)` on `𝒵₊`. Then the
interpolated process `z̄(t) = z̄_n + (t − τ_n)(z̄_{n+1} − z̄_n)/γ_{n+1}` (`t ∈ [τ_n, τ_{n+1})`,
`τ_n = Σ_{k=0}^n γ_k`, `z̄_n = (x_{n−1}, m_n, v_n)`) is almost surely a bounded asymptotic
pseudotrajectory of `Φ`. -/
theorem interp_isAPT {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : AdamDyn.WellPosed.Vec d → Ξ → ℝ) (gf : AdamDyn.WellPosed.Vec d → Ξ → AdamDyn.WellPosed.Vec d) (ξ : ℕ → Ω → Ξ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.WellPosed.Vec d)
    (hε : 0 < ε)
    (h22 : Assumption22 μ f gf)
    (h23 : Tendsto (AdamDyn.ConstStep.objective μ f) (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (h24 : ∀ x i, 0 < AdamDyn.ConstStep.sqGradMean μ gf x i)
    (h41 : Assumption41 P μ ξ)
    (h51 : Assumption51 γ α β a b)
    (h42 : Assumption42i μ gf 4)
    (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hbdd : ∀ᵐ ω ∂P, Bornology.IsBounded (Set.range fun n => adamIter gf γ α β ε x0 ξ n ω))
    (Φ : Flow ℝ≥0 (AdamDyn.ODEConv.Zplus d))
    (hΦ : AdamDyn.ODEConv.IsODEInfSemiflow a b ε (AdamDyn.ConstStep.objective μ f) (AdamDyn.ConstStep.sqGradMean μ gf) Φ) :
    ∀ᵐ ω ∂P,
      StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ
          (fun t : ℝ≥0 => AdamDyn.ODEConv.toZplus (interpProcess γ
            (zbar (fun k => adamIter gf γ α β ε x0 ξ k ω)) (t : ℝ))) ∧
        Bornology.IsBounded (Set.range fun t : ℝ≥0 =>
          interpProcess γ (zbar (fun k => adamIter gf γ α β ε x0 ξ k ω)) (t : ℝ)) := by sorry

end AdamDyn.DecConv
