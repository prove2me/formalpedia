-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_lemma_4_7
-- name    : AccelNewtonDinkelbach.Supplement.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:04:50.212326+00:00
-- url     : https://prove2.me/theorems/fd90b7d8-2830-476d-a4eb-903ae4f4a705
-- title:
--   Lemma 4.7 — warm-started Grapevine returns an optimum or certifies $f(\delta')=-\infty$
-- statement:
--   Given an optimal dual solution $y\in\mathbb R^n$ for $f(\delta)$ and $\delta'<\delta$, put $\bar y_{u'}=\delta'$ and $\bar y_v=y_v$. For every Grapevine tie-break, its output labels are finite on $V$ and keep $u'$ at $\delta'$. If the restriction to $V$ is not dual feasible for $f(\delta')$, then $f(\delta')=-\infty$; otherwise it is dual optimal and the returned walk is a shortest path from $u$ with respect to the input labels $\bar y$.
--
--   Differences from the source:
--   - generalization: the full split graph G_u → the split graph of an arbitrary active arc subgraph A; reason: all arcs recovers the source and Algorithm 3 applies the lemma to G^(k)
--   - encoding: labels in R^n and R^(n+1) → split-node labels in EReal with finiteness of the output on V included in the conclusion; reason: Algorithm 3 also uses +∞ labels, while this lemma's real input yields real output
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.7, p.14

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPIFractional
import Definitions.Def_AccelNewtonDinkelbach_Supplement_Grapevine

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Lemma 4.7 (warm-started Grapevine solves the next dual LP).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.7, p.14.
The universal quantification over Grapevine outputs includes every allowed tie-break. -/
theorem lemma_4_7 {n m : ℕ} (M : M2VPI n m) (A : Fin m → Prop) (u : Fin n)
    (δ δ' : ℝ) (hδ : δ' < δ) (y : Fin n → ℝ) (hy : M.DualOptimal A u δ y) :
    let input : M2VPI.SplitNode n → EReal := fun v =>
      match v with | none => (δ' : EReal) | some w => (y w : EReal)
    ∀ (output : M2VPI.SplitNode n → EReal) (P : M.SplitWalk A u),
      M.Grapevine A u input output P →
      ∃ z : Fin n → ℝ, (∀ v, output (some v) = (z v : EReal)) ∧ output none = (δ' : EReal) ∧
        ((¬ M.DualFeasible A u δ' z → M.paramF A u δ' = ⊥) ∧
          (M.DualFeasible A u δ' z → M.DualOptimal A u δ' z ∧ P.IsShortest input)) := by sorry

end AccelNewtonDinkelbach.Supplement
