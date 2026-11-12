-- Prove2me | Theorems.Thm_ConvexRMDP_fixed_point_nonneg
-- name    : ConvexRMDP.fixed_point_nonneg
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:18:03.895638+00:00
-- url     : https://prove2.me/theorems/0b27ae1d-4ad8-4a0c-a1f4-92bd1bafeed5
-- title:
--   Proof of Theorem 4.1: $\tilde v^\star \ge 0$, so (4.6) may be restricted to $v \ge 0$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP (in particular $r_{sa} \ge 0$) with $\mathcal A$ nonempty, let $b > 0$, and let $\tilde v^\star$ be a fixed point of the regularized robust Bellman operator $\tilde T$. Then $\tilde v^\star \ge 0$ componentwise, and $\tilde v^\star$ is still an optimal solution of the program (4.6) with the domain restricted to nonnegative vectors:
--   $$
--   \sum_{s} \exp_b(\tilde v^\star_s) = \max\Big\{\sum_{s} \exp_b(v_s) \;\Big|\; v \le \tilde T(v),\ v \ge 0,\ v \in \mathbb R^{\mathcal S}\Big\}.
--   $$
--
--   After the change of variables $x = \exp_b(v)$ the constraint $v \ge 0$ becomes $x \ge 1$, which is the lower bound in the convex program (4.7).
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
--   - encoding: we can restrict the domain {v | v ≤ T̃(v)} to {v | v ≤ T̃(v), v ≥ 0} → ṽ⋆ is feasible for the restricted program and its objective value is maximal there (IsGreatest); reason: restricting the domain keeps the optimum because the optimum ṽ⋆ lies in the smaller set.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), proof of Theorem 4.1, p.14, "Recall that ṽ⋆ ≥ 0, and therefore we can restrict the domain …"

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **`ṽ⋆ ≥ 0` and the restricted program** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.14, proof
of Theorem 4.1, "Recall that ṽ⋆ ≥ 0, …"): the fixed point `ṽ⋆` of `T̃` is nonnegative, and therefore
it is still optimal for (4.6) restricted to `{v ∈ ℝ^S | v ≤ T̃(v), v ≥ 0}`.

**Formalization Note.** The nonnegativity uses the standing assumption `r ≥ 0` (a field of
`RMDP`). The restricted program's optimum is stated with `IsGreatest`: `ṽ⋆` is feasible and its
objective value `∑_s exp_b(ṽ⋆_s)` is maximal. `A` is nonempty and `b > 0`. -/
theorem fixed_point_nonneg {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (vt : S → ℝ) (hvt : M.regOp b vt = vt) :
    0 ≤ vt ∧
      IsGreatest ((fun v : S → ℝ => ∑ s, expB b (v s)) '' {v | v ≤ M.regOp b v ∧ 0 ≤ v})
        (∑ s, expB b (vt s)) := by sorry

end ConvexRMDP
