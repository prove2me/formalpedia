-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_21
-- name    : BlockLewisIPM.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:26.8542+00:00
-- url     : https://prove2.me/theorems/f7f0e5bf-6d56-42db-babf-2ac7740f5c25
-- title:
--   Lemma 21 — Lewis weights are stable under squared block scaling
-- statement:
--   Let $p\in(0,2]$, and let $A\in\mathbb R^{n\times d}$ have full column rank. For symmetric positive definite block diagonal $C,C'$ with blocks $C_i,C'_i$, and for $\epsilon>0$,
--
--   $$C_i^2\approx_{2\epsilon}(C_i')^2\ \text{ for all }i\quad\Longrightarrow\quad w(C)\approx_{8\epsilon}w(C').$$
--
--   So the preconditioned Lewis weights depend only on the block squares, and depend on them stably.
--
--   Differences from the source:
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 21, p.16

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 21**, p.16. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear
Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** `C = diag(C_i)` and `C′ = diag(C′_i)` are given by their blocks, positive
definite and so symmetric. `A` has full column rank (reading R10). The `ϵ` here is free, unrelated to
Algorithm 1's. `w(C) = w_p(CA)` with `v = (d/m) 1_m` (Definition 13). -/
theorem lemma_21 {ι : Type} [Fintype ι] [DecidableEq ι] {dim : ι → ℕ} {d : ℕ}
    (A : Matrix (BIdx dim) (Fin d) ℝ) (hA : FullColRank A) (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 2)
    (Cb Cb' : ∀ i, Matrix (Fin (dim i)) (Fin (dim i)) ℝ)
    (hC : ∀ i, (Cb i).PosDef) (hC' : ∀ i, (Cb' i).PosDef) (ϵ : ℝ) (hϵ : 0 < ϵ)
    (h : ∀ i, ApproxEq (2 * ϵ) (Cb i ^ 2) (Cb' i ^ 2)) :
    VecApproxEq (8 * ϵ) (lewisC p A (Matrix.blockDiagonal' Cb))
      (lewisC p A (Matrix.blockDiagonal' Cb')) := by sorry

end BlockLewisIPM
