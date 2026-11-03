-- Prove2me | Theorems.Thm_ConvexRMDP_display_4_3
-- name    : ConvexRMDP.display_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:20.47427+00:00
-- url     : https://prove2.me/theorems/a2b4bb86-4b9c-4bc9-a31e-e82e2ca6aba7
-- title:
--   Display (4.3): $\tilde T(v)_s = \frac1b\log\sum_a \frac{1}{|A|}\exp(b r_{sa} + b\gamma\min_{p\in\mathcal U_{sa}} p^\top v)$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty and let $b > 0$. For every $v \in \mathbb R^{\mathcal S}$ and every $s \in \mathcal S$ the regularized robust Bellman operator with uniform reference policy satisfies
--   $$
--   \tilde T(v)_s = \frac1b \log\left(\sum_{a \in \mathcal A} \frac{1}{|\mathcal A|} \exp\left(b \cdot r_{sa} + b \cdot \gamma \min_{p \in \mathcal U_{sa}} p^\top v\right)\right).
--   $$
--
--   This closed form, obtained from Lemma 4.1, is the starting point of the exponential change of variables of §4.2.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - reading: regularization scalar b in (4.1) → b > 0; reason: the paper's setting of §4.2 ("For b > 0"); with b ≤ 0 the term −(1/b)KL is not a regularizer.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), display (4.3), p.11 (restated on p.12)

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp

namespace ConvexRMDP

/-- **Display (4.3)** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.11): applying Lemma 4.1 to `T̃`,
`T̃(v)_s = (1/b) log(∑_a (1/|A|) exp(b · r_{sa} + b · γ min_{p ∈ 𝒰_{sa}} pᵀv))` for every `s`.

**Formalization Note.** `min_{p ∈ 𝒰_{sa}} pᵀv` is `M.worst v s a` (an infimum over the nonempty
set `𝒰_{sa}`); `A` is nonempty and `b > 0`. -/
theorem display_4_3 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (v : S → ℝ) (s : S) :
    M.regOp b v s = Real.log (∑ a, (1 / (Fintype.card A : ℝ)) *
      Real.exp (b * M.r s a + b * M.γ * M.worst v s a)) / b := by sorry

end ConvexRMDP
