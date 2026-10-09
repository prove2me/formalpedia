-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_theorem_1_reduction
-- name    : ExpanderBIS.HardCore.theorem_1_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:15.259222+00:00
-- url     : https://prove2.me/theorems/c823f49c-ea41-49ea-a934-c0bdd5f45ecc
-- title:
--   Theorem 1 (core) — on bipartite α-expanders, Z_G(λ) reduces to two polymer models satisfying the Kotecký–Preiss condition
-- statement:
--   Let $\alpha > 0$ and $\Delta \ge 3$, and let $G$ be a bipartite $\alpha$-expander with classes $\mathcal O, \mathcal E$, maximum degree at most $\Delta$ and $n \ge 3$ vertices. Let
--   $$\lambda > \max\left\{(2e^3\Delta^4)^{1/\alpha},\ e^{11/\alpha}\right\}.$$
--   Then:
--
--   1. **Reduction.** $(1+\lambda)^{|\mathcal O|}\,\Xi^{\mathcal E}(G) + (1+\lambda)^{|\mathcal E|}\,\Xi^{\mathcal O}(G)$ is an $e^{-n}$-relative approximation to the hard-core partition function $Z_G(\lambda)$.
--   2. **Kotecký–Preiss condition.** For each of the two polymer models (even and odd) and every polymer $\gamma$ of that model,
--   $$\sum_{\gamma' :\, d(\gamma',\gamma) \le 1} w_{\gamma'}\, e^{g(\gamma') + |\gamma'|} \le |\gamma|, \qquad g(\gamma') = |\gamma'|,$$
--   where the sum runs over the polymers $\gamma'$ of the same model that are incompatible with $\gamma$ ($d_G(\gamma',\gamma) \le 2$, i.e. distance at most $1$ in $G^2$), including $\gamma' = \gamma$.
--
--   This is the mathematical content of Theorem 1 of the paper (an FPTAS and a polynomial-time sampler for the hard-core model at high fugacity on bounded-degree bipartite expanders). The algorithm itself, obtained from these two facts by truncating the cluster expansion (Theorem 8 of the paper, adapted from Helmuth, Perkins and Regts), is not part of this statement.
--
--   **Formalization Note** Theorem 1 states the threshold as $\lambda > C\Delta^{4/\alpha}$ for an absolute constant $C$; the threshold above is the one its proof (§4.3) uses. The hypothesis $n \ge 3$ is added because Lemma 18, and with it the reduction, fails on the edgeless graph with one vertex in each class. The polymer weights are nonnegative reals, so $|w_{\gamma'}|$ of the general condition is written $w_{\gamma'}$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 3, Theorem 1; proof in §§4.1–4.3, pp. 18–22 (Lemma 20, p. 19; the Kotecký–Preiss display with g(γ) = |γ|, p. 21; the threshold λ > max{(2e³Δ⁴)^{1/α}, e^{11/α}}, §4.3, p. 21)

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

open Classical in
theorem theorem_1_reduction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α lam : ℝ) (Δ : ℕ)
    (hα : 0 < α) (hΔ : 3 ≤ Δ) (hn : 3 ≤ Fintype.card V)
    (hbip : IsBipartiteWrt G O) (hdeg : ∀ v, G.degree v ≤ Δ) (hG : IsBipExpander G O α)
    (hlam : max ((2 * Real.exp 3 * (Δ : ℝ) ^ 4) ^ (1 / α)) (Real.exp (11 / α)) < lam) :
    ExpanderBIS.Potts.IsRelApprox (Real.exp (-(Fintype.card V : ℝ)))
        ((1 + lam) ^ #O * sideXi G (univ \ O) lam + (1 + lam) ^ #(univ \ O) * sideXi G O lam)
        (hardcoreZ G lam) ∧
    ∀ side : Finset V, (side = O ∨ side = univ \ O) → ∀ γ ∈ sidePolymers G side,
      ∑ γ' ∈ (sidePolymers G side).filter (fun γ' => ¬ Compat2 G γ' γ),
          hcWeight G lam γ' * Real.exp ((#γ' : ℝ) + (#γ' : ℝ)) ≤ (#γ : ℝ) := by sorry

end ExpanderBIS.HardCore
