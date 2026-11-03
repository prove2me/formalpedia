-- Prove2me | Theorems.Thm_ConvexRMDP_proposition_4_1_item_1
-- name    : ConvexRMDP.proposition_4_1_item_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:09.114286+00:00
-- url     : https://prove2.me/theorems/ca5e3dc1-03f9-4e7f-bd9c-7c448c4a19b9
-- title:
--   Proposition 4.1, item 1: $\tilde T$ is a monotone $\gamma$-contraction for the $\ell_\infty$ norm
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty, let $b > 0$, and let $\tilde T$ be the regularized robust Bellman operator with the uniform reference policy $\nu_{sa} = 1/|\mathcal A|$. Then $\tilde T$ is monotone,
--   $$
--   v \le v' \implies \tilde T(v) \le \tilde T(v'),
--   $$
--   and it is a contraction for the $\ell_\infty$ norm with modulus $\gamma$:
--   $$
--   \|\tilde T(v_1) - \tilde T(v_2)\|_\infty \le \gamma \|v_1 - v_2\|_\infty \qquad \text{for all } v_1, v_2 \in \mathbb R^{\mathcal S}.
--   $$
--
--   Consequently $\tilde T$ has a unique fixed point $\tilde v^\star$, and Lemma 3.1 applies to it.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - reading: regularization scalar b in (4.1) → b > 0; reason: the paper's setting of §4.2 ("For b > 0"); with b ≤ 0 the term −(1/b)KL is not a regularizer.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
--   - generalization: T̃ is a contraction with respect to the ℓ∞ norm → ContractingWith γ (modulus exactly γ); reason: Appendix B proves this modulus; it implies the printed claim since γ < 1.
--   - encoding: ℝ^S with componentwise order and ℓ∞ norm → S → ℝ with the Pi order and the sup metric; reason: Lean convention; identical order and metric.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), Proposition 4.1, item 1, p.11 (proof in Appendix B, pp.27–28)

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp

namespace ConvexRMDP

/-- **Proposition 4.1, item 1** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.11; proof in App. B,
pp.27–28): with the uniform reference policy `ν_{sa} = 1/|A|`, the regularized robust Bellman
operator `T̃` is a monotone contraction for the `ℓ∞` norm.

**Formalization Note.** The contraction modulus is the discount factor `γ`, the constant App. B
derives (`‖T̃(v₁) − T̃(v₂)‖_∞ ≤ γ‖v₁ − v₂‖_∞`); this implies the printed "contraction". `ℝ^S` is
`S → ℝ` with the componentwise order and the sup metric. `A` is nonempty and `b > 0` (the
regularization scalar of §4). -/
theorem proposition_4_1_item_1 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    Monotone (M.regOp b) ∧ ContractingWith ⟨M.γ, M.γ_pos.le⟩ (M.regOp b) := by sorry

end ConvexRMDP
