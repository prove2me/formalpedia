-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_proposition_2
-- name    : CCPCollateral.Incentive.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:26.099233+00:00
-- url     : https://prove2.me/theorems/48c5541d-ea71-4f29-8551-08d82ef37b52
-- title:
--   Proposition 2, p. 19 — all members hedge iff F ≥ F̂(I); F̂ solves (18) uniquely, is piecewise linear, strictly decreasing, convex, slope ≥ −1 (> −1 if N F̂(0) ≤ (N−1)D)
-- statement:
--   Consider $N\ge 2$ clearing members of a central counterparty under the standing assumptions of the setting. Each member chooses to hedge ($s$) or to risk-shift ($r$), and member $i$'s expected profit is the value (13), which depends on the collateral (initial margin $I$, default fund $F$) and on how many other members hedge. Let $\hat F(I)$ be the least default fund that makes hedging a best response when all other members hedge, and $\hat I(0)$ the least initial margin that does so with $F=0$.
--
--   1. **Equilibrium (17).** For every $I,F\ge0$ with $I+F\le D$, the hedging game has exactly one Pareto-dominant Nash equilibrium, and in it
--   $$a(I,F)=\begin{cases} r\ \text{for all } i, & 0\le F<\hat F(I),\\ s\ \text{for all } i, & \hat F(I)\le F\le D-I.\end{cases}$$
--   2. **Equation (18).** For every $I\in[0,\hat I(0)]$, $0\le\hat F(I)<D-I$ and $\hat F(I)$ is the unique $F\in[0,D-I)$ with
--   $$D-I-F+X^{N-1}(I,F)=(A_{CCP}-I-F)\,\mathcal P.$$
--   3. **Shape.** On $[0,\hat I(0)]$ the function $\hat F$ is piecewise linear (affine between finitely many breakpoints), strictly decreasing, continuous and convex, and $I\mapsto\hat F(I)+I$ is nondecreasing (slope $\ge-1$). If $N\hat F(0)\le(N-1)D$, then $I\mapsto \hat F(I)+I$ is strictly increasing (slope $>-1$).
--
--   The proposition identifies the incentive-compatible collateral: a default fund at least $\hat F(I)$ is exactly what makes "all hedge" the outcome, and initial margin and default fund are substitutes at a rate of at most one for one.
--
--   **Formalization Note** "Pareto-dominant Nash equilibrium" is a pure-strategy Nash equilibrium giving every member at least its payoff in any Nash equilibrium; (17) is stated as an iff over all profiles, which asserts existence and uniqueness. The claims about $\hat F$ are stated on $[0,\hat I(0)]$, where (18) has a root; for $I>\hat I(0)$, $\hat F(I)=0$ and (17) still holds. "Continuous and convex at the set of kinks" is rendered as continuity and convexity on $[0,\hat I(0)]$. The page asserts "slope greater than $-1$" unconditionally; this fails when $N\hat F(0)>(N-1)D$, where the prefunded default fund covers the shortfall of all $N-1$ other members and $\hat F$ has slope exactly $-1$ on an initial interval (for example $N=2$, $q_s=1/10$, $q_r=1/2$, $R_s=3/2$, $R_r=13/5$, $p_c=1/2$, $A_0=11/10$, $\gamma=1$, $\alpha=1/2$, $\delta=1/10$, $D=1$, where $\hat F(I)=3/4-I$ on $[0,1/2]$). The statement therefore asserts slope $\ge-1$ always and slope $>-1$ under $N\hat F(0)\le(N-1)D$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), Proposition 2, (17)–(18), p. 19

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- Proposition 2 (p. 19). (17): for collateral `0 ≤ I`, `0 ≤ F`, `I + F ≤ D`, the Pareto-dominant
Nash equilibrium exists, is unique, and is "all not hedging" if `F < F̂(I)` and "all hedging" if
`F̂(I) ≤ F`. (18): for `I ∈ [0, Î(0)]`, `F̂(I)` is the unique root of (18) in `[0, D − I)`. On
`[0, Î(0)]`, `F̂` is piecewise linear, strictly decreasing, with slope `≥ −1` (and `> −1` when
`N F̂(0) ≤ (N − 1) D`; the page states `> −1` unconditionally, which fails otherwise), continuous
and convex. -/
theorem proposition_2 (m : Params) (hm : Standing m) :
    (∀ I F : ℝ, 0 ≤ I → 0 ≤ F → I + F ≤ m.D → ∀ a : Fin m.N → Action,
      m.IsParetoDominantNash I F a ↔
        a = fun _ => if F < m.Fhat I then Action.r else Action.s) ∧
    (∀ I ∈ Set.Icc 0 m.Ihat0, 0 ≤ m.Fhat I ∧ m.Fhat I < m.D - I ∧ m.Eq18 I (m.Fhat I) ∧
      ∀ F, 0 ≤ F → F < m.D - I → m.Eq18 I F → F = m.Fhat I) ∧
    (∃ (n : ℕ) (c : Fin (n + 2) → ℝ), StrictMono c ∧ c 0 = 0 ∧ c (Fin.last _) = m.Ihat0 ∧
      ∀ j : Fin (n + 1), ∃ u v : ℝ,
        ∀ I ∈ Set.Icc (c j.castSucc) (c j.succ), m.Fhat I = u * I + v) ∧
    StrictAntiOn m.Fhat (Set.Icc 0 m.Ihat0) ∧
    MonotoneOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0) ∧
    ((m.N : ℝ) * m.Fhat 0 ≤ ((m.N : ℝ) - 1) * m.D →
      StrictMonoOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0)) ∧
    ContinuousOn m.Fhat (Set.Icc 0 m.Ihat0) ∧
    ConvexOn ℝ (Set.Icc 0 m.Ihat0) m.Fhat := by sorry

end CCPCollateral.Incentive
