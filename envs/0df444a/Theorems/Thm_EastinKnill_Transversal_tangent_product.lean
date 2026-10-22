-- Prove2me | Theorems.Thm_EastinKnill_Transversal_tangent_product
-- name    : EastinKnill.Transversal.tangent_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:35.805803+00:00
-- url     : https://prove2.me/theorems/daa9307d-fd38-48bc-9c89-213f20f797a8
-- title:
--   Proof of Theorem 1, p. 3 — the Lie algebra of $\mathcal T$: $D=\sum_j H_j$ with $H_j$ local Hermitian
-- statement:
--   Let $\mathcal Q$ be a composite system of finitely many subsystems and $\mathcal T$ its group of unitary product operators. Let $D$ be a Hermitian operator on $\mathcal Q$ whose one-parameter group lies in $\mathcal T$: $e^{itD} \in \mathcal T$ for every real $t$. Then there are Hermitian operators $H_j$ on the subsystems with
--
--   $$D = \sum_j I\otimes H_j \otimes I,$$
--
--   where $I\otimes H_j\otimes I$ acts as $H_j$ on subsystem $j$ and as the identity elsewhere.
--
--   This identifies the Lie algebra $\mathfrak t$ of $\mathcal T$ as the sums of local Hermitian operators; in the proof of Theorem 1 it is applied to the Lie algebra $\mathfrak c \subseteq \mathfrak t$ of the identity component of the logical product unitaries.
--
--   **Formalization Note** Membership $D\in\mathfrak t$ is expressed through the one-parameter group, which is the definition of the Lie algebra of a closed matrix group (with the factor $i$ of footnote 1). The paper writes $D = \sum_j \alpha_j H_j$ with $\alpha_j$ real; since $\alpha_j H_j$ is again Hermitian, the coefficients are absorbed into $H_j$, which is equivalent.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Theorem 1, display "D = Σ_{j=1}^n α_j H_j"

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem tangent_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (D : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hD : D.IsHermitian)
    (h : ∀ t : ℝ, ∃ U ∈ productUnitaries α,
      (U : Matrix (∀ j, α j) (∀ j, α j) ℂ) = NormedSpace.exp (((t : ℂ) * Complex.I) • D)) :
    ∃ H : ∀ j, Matrix (α j) (α j) ℂ, (∀ j, (H j).IsHermitian) ∧
      D = ∑ j, localOp α j (H j) := by sorry

end EastinKnill.Transversal
