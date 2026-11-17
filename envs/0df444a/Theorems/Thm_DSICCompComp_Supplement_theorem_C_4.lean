-- Prove2me | Theorems.Thm_DSICCompComp_Supplement_theorem_C_4
-- name    : DSICCompComp.Supplement.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:35:46.213903+00:00
-- url     : https://prove2.me/theorems/3490a7ea-7baf-4d78-9fa0-b3433977cb7f
-- title:
--   Theorem C.4 — DSIC duality: revenue $\le$ $\Phi^\lambda$-virtual welfare, equality iff slackness, and the optimal pair
-- statement:
--   Consider the finite-support setting of Appendix C: $n$ independent bidders and $m$ items, bidder $i$'s values drawn from $D_i$ with finite support and PMF $f_i > 0$, joint PMF $f(v) = \prod_i f_i(v_i)$ on $\mathrm{supp}(D)$, and a non-participation type $\varnothing$. Let $P^+(D)$ be the feasible set of the DSIC revenue LP, $P(D)$ the polyhedron of its non-DSIC constraints, $L(\lambda, x, p)$ the partial Lagrangian that Lagrangifies the DSIC constraints, and $\Phi^\lambda$ the virtual value function of Definition C.3.
--
--   **Theorem.**
--
--   1. If $\lambda \ge 0$ satisfies flow conservation, then for all $(x, p) \in P^+(D)$ the revenue of $(x, p)$ is at most the virtual welfare of $x$ with respect to $\Phi^\lambda$:
--   $$
--   \mathbb E\Big[\sum_i p_i(v)\Big] \;\le\; \mathbb E\Big[\sum_i x_i(v)\cdot \Phi^\lambda_i(v)\Big].
--   $$
--   2. For such $\lambda$ and $(x, p)$, equality holds if and only if for all bidders $i$, values $v_i \in \mathrm{supp}(D_i)$, reports $v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}$ and profiles $v_{-i}$ with $\lambda^{v_{-i}}_i(v_i, v'_i) > 0$, the corresponding DSIC constraint binds.
--   3. If $(x^*, p^*)$ is a revenue-optimal DSIC/IR mechanism (an optimal solution of the LP) and $\lambda^*$ is an optimal dual solution (a minimizer of $g(\lambda) = \max_{(x,p)\in P(D)} L(\lambda, x, p)$ over $\lambda \ge 0$), then the revenue of $(x^*, p^*)$ equals the virtual welfare of $x^*$ with respect to $\Phi^{\lambda^*}$, and
--   $$
--   (x^*, p^*) \in \arg\max_{(x, p) \in P(D)} \sum_{v \in \mathrm{supp}(D)} f(v) \sum_i x_i(v)\cdot \Phi^{\lambda^*}_i(v).
--   $$
--
--   This is the DSIC analogue of the Cai–Devanur–Weinberg duality framework: because there is a DSIC constraint for every profile $v_{-i}$ of the other bidders, the flow $\lambda^{v_{-i}}_i$ may depend on $v_{-i}$. The paper uses it, through a discretization limit, to upper-bound the optimal DSIC revenue in the proof of Theorem 4.1.
--
--   **Formalization Note** A dual solution is `lam i v w` $= \lambda^{v_{-i}}_i(v_i, w)$ with $v \in \mathrm{supp}(D)$ a full profile and `none` $= \varnothing$. Part 3 does not assume flow conservation of $\lambda^*$, nor strong duality.
--
--   Differences from the source:
--
--   - generalization: D_i = ×_j D_ij with values in ℝ≥0^m and finite support → an arbitrary positive PMF f_i on an arbitrary finite set S_i ⊆ ℝ^m; reason: neither independence of items within a bidder nor nonnegativity of values is used; the page's setting is the special case of product PMFs on nonnegative vectors
--   - reading: λ^{v_{-i}}_i(v_i, v'_i), 'the Lagrange multiplier corresponding to the DSIC constraint' → λ ≥ 0 as a hypothesis of parts 1–2, and the dual minimized over λ ≥ 0 in part 3; reason: multipliers of inequality constraints are nonnegative and the proof uses it ('the terms ... multiplied by dual variables is nonnegative'); flow conservation of λ* is not assumed (the paper derives it by Lemma C.2)
--   - encoding: λ^{v_{-i}}_i(v_i, v'_i) for i, v_{-i}, v_i ∈ supp(D_i), v'_i ∈ supp(D_i) ∪ {∅} → lam i v w with v ∈ supp(D) the full profile and w : Option (S i); reason: a bijective re-indexing ((v_{-i}, v_i) ↔ v)
--   - encoding: variables x_ij(v), p_i(v) at v ∈ supp(D) and at (∅, v_{-i}) → x, p defined on all report profiles in ×_i (S_i ∪ {∅}); reason: the extra variables (two or more ∅ entries) occur in no constraint, objective or Lagrangian
--   - encoding: g(λ) = max_{(x,p)∈P(D)} L(λ, x, p) → the supremum in EReal; reason: it equals the maximum when finite and represents +∞ when L is unbounded above (Lemma C.2)
--   - encoding: Φ^λ defined for flow-conserving λ → the same formula for every λ; reason: it is used only with flow-conserving λ in parts 1–2, and in part 3 λ* conserves flow by Lemma C.2
--   - encoding: (x*, p*) ∈ argmax_{(x,p)∈P(D)} Σ_v f(v) Σ_i x_i(v)·Φ^{λ*}_i(v) → (x*, p*) ∈ P(D) and its virtual welfare is ≥ that of every (x, p) ∈ P(D); reason: the definition of argmax
--   - encoding: 'the corresponding DSIC constraint binds' → dsicSlack E sol v i w = 0; reason: dsicSlack is the difference of the two sides of that constraint
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Theorem C.4, p.36 (pdf p.37); setting and LP, Appendix C, pp.34–35 (pdf pp.35–36); Definitions C.1 and C.3, pp.35–36 (pdf pp.36–37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_FlowConservation
import Definitions.Def_DSICCompComp_Supplement_virtualWelfare
import Definitions.Def_DSICCompComp_Supplement_IsOptimalDual
import Definitions.Def_DSICCompComp_Supplement_IsRevenueOptimal

namespace DSICCompComp

namespace Supplement

/-- Theorem C.4 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Theorem C.4, p.36 (pdf p.37)): if `λ` satisfies flow conservation, then for all `(x, p) ∈ P⁺(D)`,
the revenue of `(x, p)` is at most the virtual welfare of `x` with respect to `Φ^λ`:
`E[∑_i p_i(v)] ≤ E[∑_i x_i(v)·Φ^λ_i(v)]`. Equality holds if and only if for all bidders `i`, values
`v_i ∈ supp(D_i)`, `v'_i ∈ supp(D_i) ∪ {∅}` and profiles `v_{-i}` with `λ^{v_{-i}}_i(v_i, v'_i) > 0`, the
corresponding DSIC constraint binds. If `(x*, p*)` is a revenue-optimal DSIC/IR mechanism and `λ*` is
an optimal dual solution, then the revenue of `(x*, p*)` coincides with the virtual welfare of `x*`
with respect to `Φ^{λ*}` and `(x*, p*) ∈ argmax_{(x,p) ∈ P(D)} ∑_{v} f(v)·∑_i x_i(v)·Φ^{λ*}_i(v)`.

**Formalization Note** The three conjuncts are the three sentences. Dual variables are Lagrange
multipliers of inequality constraints, so `λ ≥ 0` is part of the setting in the first two parts, and
the dual is minimized over `λ ≥ 0` in the third; flow conservation of `λ*` is not assumed in the third
part (the paper derives it from optimality, Lemma C.2). Dual solutions are encoded as in
`FlowConservation`: `lam i v w = λ^{v_{-i}}_i(v_i, w)`. -/
theorem theorem_C_4 {n m : ℕ} (E : FiniteSetting n m) :
    (∀ lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ,
      (∀ i v w, 0 ≤ lam i v w) → FlowConservation E lam →
        ∀ sol : LPSolution E, InPPlus E sol → lpRevenue E sol ≤ virtualWelfare E lam sol) ∧
    (∀ lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ,
      (∀ i v w, 0 ≤ lam i v w) → FlowConservation E lam →
        ∀ sol : LPSolution E, InPPlus E sol →
          (lpRevenue E sol = virtualWelfare E lam sol ↔
            ∀ (i : Fin n) (v : (k : Fin n) → E.S k) (w : Option (E.S i)),
              0 < lam i v w → dsicSlack E sol v i w = 0)) ∧
    (∀ (solStar : LPSolution E)
        (lamStar : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ),
      IsRevenueOptimal E solStar → IsOptimalDual E lamStar →
        lpRevenue E solStar = virtualWelfare E lamStar solStar ∧
          InP E solStar ∧
          ∀ sol : LPSolution E, InP E sol →
            virtualWelfare E lamStar sol ≤ virtualWelfare E lamStar solStar) := by sorry

end Supplement

end DSICCompComp
