-- Prove2me | Theorems.Thm_ConvexRMDP_change_of_variables
-- name    : ConvexRMDP.change_of_variables
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:55.337952+00:00
-- url     : https://prove2.me/theorems/d62bf951-4bca-4983-b43c-242112d709d7
-- title:
--   §4.2, p.13: $v \le \tilde T(v) \iff \exp_b(v) \le \tilde t(\exp_b(v))$, and $\{x > 0 \mid x \le \tilde t(x)\}$ is convex
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty and let $b > 0$. With the change of variables $x = \exp_b(v)$, i.e. $x_s = e^{b v_s}$:
--
--   1. for every $v \in \mathbb R^{\mathcal S}$,
--   $$
--   v \le \tilde T(v) \iff \exp_b(v) \le \tilde t\big(\exp_b(v)\big),
--   $$
--   so that $v \le \tilde T(v)$ if and only if $x \le \tilde t(x)$;
--   2. the set $\{x \in (\mathbb R^*_+)^{\mathcal S} \mid x \le \tilde t(x)\}$ is convex.
--
--   Inequalities between vectors are componentwise. This is the step that turns the non-convex constraint $v \le \tilde T(v)$ into a convex one.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
--   - encoding: x ∈ (ℝ*₊)^S with x = exp_b(v), and x ≤ t̃(x) → the equivalence stated for exp_b(v); reason: every positive vector is exp_b of its log_b, so this is the equivalence on (ℝ*₊)^S.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §4.2, p.13, "We now obtain v ≤ T̃(v) ⇐⇒ … ⇐⇒ x ≤ t̃(x)"

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **The exponential change of variables** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.13,
"We now obtain …"): with `x = exp_b(v)`,
`v ≤ T̃(v) ⇔ exp_b(v) ≤ t̃(exp_b(v)) ⇔ x ≤ t̃(x)`, and the set `{x ∈ (ℝ*₊)^S | x ≤ t̃(x)}` is convex.

**Formalization Note.** Orders on `S → ℝ` are componentwise. `exp_b(v)` is
`fun s => expB b (v s)`; every positive vector is of this form, so the first clause is the
equivalence on `(ℝ*₊)^S`. `A` is nonempty and `b > 0`. -/
theorem change_of_variables {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∀ v : S → ℝ, v ≤ M.regOp b v ↔
        (fun s => expB b (v s)) ≤ M.tOp b (fun s => expB b (v s))) ∧
      Convex ℝ {x : S → ℝ | (∀ s, 0 < x s) ∧ x ≤ M.tOp b x} := by sorry

end ConvexRMDP
