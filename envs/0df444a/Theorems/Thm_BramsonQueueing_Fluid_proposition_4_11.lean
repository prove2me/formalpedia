-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_11
-- name    : BramsonQueueing.Fluid.proposition_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:51.604192+00:00
-- url     : https://prove2.me/theorems/5dab6a50-2747-4ec5-a4b2-5ad52331e6f1
-- title:
--   Proposition 4.11 — Traffic and stability properties of fluid models
-- statement:
--   Let a fluid model include the basic equations for an open network, and write $\rho_j$ for station $j$'s load. All four conclusions hold:
--
--   1. If $\sum_j\rho_j<1$, the model is stable.
--   2. Every solution satisfies
--   $$\liminf_{t\to\infty}\frac{Y(t)}t\ge e-\rho.$$
--   The lower bound is uniform over all solutions with bounded $|Z(0)|$: for each bound $B\ge0$ and $\eta>0$, one time threshold works for every such solution and station, with lower bound $1-\rho_j-\eta$. If $Z(0)=0$, then $Y(t)\ge(e-\rho)t$ for every $t\ge0$.
--   3. If one solution has $Z_k(t)<Z_k(0)$ at one time for every class, then $\rho_j<1$ at every station.
--   4. If some $\rho_j>1$, there is one $\epsilon>0$ such that
--   $$|Z(t)|\ge\epsilon t\quad\text{for all times and all solutions}.$$
--
--   The model's auxiliary equations are arbitrary; no solution uniqueness or positive total arrival rate is assumed.
--
--   Differences from the source:
--   - encoding: classes 1 through K and stations 1 through J → Fin K and Fin J, with positive cardinalities and an onto station assignment; reason: this only relabels the finite classes and nonempty stations; queue populations remain unbounded
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: uniform limits or finite suprema → epsilon-threshold statements or one finite bound uniform over the stated indices; reason: these are equivalent and avoid default values for unbounded real suprema
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.11(a)–(d), printed 106 / PDF 114.

import Definitions.Def_BramsonQueueing_Fluid_FluidModel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

theorem proposition_4_11 {K J : ℕ} (d : NetworkData K J) (model : FluidModel d) :
    ((∑ j, traffic d j) < 1 → model.Stable) ∧
    (∀ B : ℝ, 0 ≤ B → ∀ ε : ℝ, 0 < ε → ∃ T : ℝ≥0, 0 < T ∧
      ∀ q, model.Solution q → mass (q.Z 0) ≤ B → ∀ t ≥ T, ∀ j,
        1 - traffic d j - ε ≤ q.Y t j / (t : ℝ)) ∧
    (∀ q, model.Solution q → q.Z 0 = 0 → ∀ (t : ℝ≥0) j,
      (1 - traffic d j) * (t : ℝ) ≤ q.Y t j) ∧
    ((∃ q, model.Solution q ∧ ∃ t, ∀ k, q.Z t k < q.Z 0 k) → Subcritical d) ∧
    ((∃ j, 1 < traffic d j) → ∃ ε : ℝ, 0 < ε ∧ ∀ q, model.Solution q →
      ∀ t : ℝ≥0, ε * (t : ℝ) ≤ mass (q.Z t)) := by sorry

end BramsonQueueing.Fluid
