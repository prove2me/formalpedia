-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_proposition_7_14
-- name    : AdamDyn.ODEConv.proposition_7_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:39.21371+00:00
-- url     : https://prove2.me/theorems/a731aa8e-6d01-43dc-8cb6-7719f45cb941
-- title:
--   Proposition 7.14 — limit sets of relatively compact APTs of a semiflow with a strict Lyapunov function
-- statement:
--   Let $\Psi$ be a semiflow on a metric space $(E, d)$ and let $z : [0, +\infty) \to E$. Assume:
--
--   1. $\Psi$ admits a strict Lyapunov function $\mathsf V$;
--   2. the set $\Lambda_\Psi$ of equilibrium points of $\Psi$ is compact;
--   3. $\mathsf V(\Lambda_\Psi)$ has an empty interior in $\mathbb R$;
--   4. $z$ is an asymptotic pseudotrajectory of $\Psi$: $z$ is continuous and for every $T > 0$, $\lim_{t\to\infty} \sup_{s \in [0,T]} d(z(t+s), \Psi_s(z(t))) = 0$;
--   5. $z([0,\infty))$ is relatively compact.
--
--   Then the limit set
--   $$ L(z) = \bigcap_{t \ge 0} \overline{z([t, \infty))} $$
--   is a compact connected subset of $\Lambda_\Psi$.
--
--   The paper quotes this from Benaïm (1999), Theorem 5.7 and Proposition 6.4; it is the bridge from the autonomous system to the non-autonomous trajectory.
--
--   **Formalization Note** Connectedness in Mathlib includes nonemptiness; $L(z)$ is nonempty here because $z$ has relatively compact range. The asymptotic pseudotrajectory and the limit set are the published definitions `StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory` and `StochApproxDyn.LimitSet.limitSet`, with time in $\mathbb R_{\ge 0}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 18, Proposition 7.14 (from Benaïm 1999, Th. 5.7 and Prop. 6.4)

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_StrictLyapunov
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory

open scoped NNReal

namespace AdamDyn.ODEConv

/-- Proposition 7.14 (Barakat & Bianchi, arXiv:1810.02263v4, p. 18, from Benaïm [5, Th. 5.7]
and [5, Prop. 6.4]). Consider a semiflow `Ψ` on a metric space `(E, d)` and a map
`z : [0, +∞) → E`. Assume: i) `Ψ` admits a strict Lyapunov function `V`; ii) the set `Λ_Ψ` of
equilibrium points of `Ψ` is compact; iii) `V(Λ_Ψ)` has an empty interior; iv) `z` is an APT of
`Ψ`; v) `z([0, ∞))` is relatively compact. Then `⋂_{t ≥ 0} cl(z([t, ∞)))` is a compact connected
subset of `Λ_Ψ`. (`IsConnected` includes nonemptiness.) -/
theorem proposition_7_14 {E : Type*} [MetricSpace E] (Ψ : Flow ℝ≥0 E) (z : ℝ≥0 → E)
    (V : E → ℝ) (hV : IsStrictLyapunovFunction Ψ V)
    (hΛ : IsCompact (equilibria Ψ))
    (hint : interior (V '' equilibria Ψ) = ∅)
    (hz : StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Ψ z)
    (hrc : IsCompact (closure (Set.range z))) :
    IsCompact (StochApproxDyn.LimitSet.limitSet z) ∧
      IsConnected (StochApproxDyn.LimitSet.limitSet z) ∧
      StochApproxDyn.LimitSet.limitSet z ⊆ equilibria Ψ := by sorry

end AdamDyn.ODEConv
