-- Prove2me | Theorems.Thm_FermionModewise_eq_18
-- name    : FermionModewise.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:04.293192+00:00
-- url     : https://prove2.me/theorems/6cc3b91f-5690-4a75-bea9-346c7e08ff59
-- title:
--   Equation (18): $\lambda_{\tilde A_i}\tilde K_{ij}=\lambda_{\tilde B_j}J_2\tilde K_{ij}J_2$; modes with different eigenvalues decouple
-- statement:
--   Let $W_A=\bigoplus_i\lambda_{\tilde A_i}J_2$ and $W_B=\bigoplus_j\lambda_{\tilde B_j}J_2$ be Williamson forms with all eigenvalues $\ge0$, and let $\tilde K$ satisfy (17), $W_A\tilde K+\tilde KW_B=0$. For an $A$-mode $i$ and a $B$-mode $j$, let $\tilde K_{ij}$ be the $2\times2$ sub-block of $\tilde K$ connecting them. Then
--   $$\lambda_{\tilde A_i}\,\tilde K_{ij}=\lambda_{\tilde B_j}\,J_2\tilde K_{ij}J_2, \tag{18}$$
--   and if $\lambda_{\tilde A_i}\ne\lambda_{\tilde B_j}$ then $\tilde K_{ij}=0$: modes in $A$ and in $B$ with different Williamson eigenvalues decouple.
--
--   Differences from the source:
--   - generalization: (17) derived from M̃² = −λ0² → (17) assumed directly; reason: (18) uses only (17), which follows from M̃² = −λ0² by eq_17
--   - encoding: K̃_ij ≡ −i⟨γ_{Ã_i}γ^T_{B̃_j}⟩ → the 2×2 submatrix of K̃ with rows (i, ·) and columns (j, ·); reason: this is the block of (16) at those modes
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (18) and the sentence after it, p.7

import Mathlib
import Definitions.Def_FermionModewise_J2
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Equation (18) and decoupling** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (18), p.7): let
`W_A = ⊕_i λ_{A_i} J₂` and `W_B = ⊕_j λ_{B_j} J₂` with all eigenvalues `≥ 0`, and let `K̃` satisfy
(17), `W_A K̃ + K̃ W_B = 0`. Then each `2 × 2` sub-block `K̃_ij` connecting A-mode `i` and B-mode `j`
satisfies `λ_{A_i} K̃_ij = λ_{B_j} J₂ K̃_ij J₂`, and if `λ_{A_i} ≠ λ_{B_j}` then `K̃_ij = 0`.

**Formalization Note.** `K̃_ij` is the submatrix of `K̃` with rows `(i, ·)` and columns `(j, ·)`. -/
theorem eq_18 {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (la : α → ℝ) (lb : β → ℝ) (hla : ∀ i, 0 ≤ la i) (hlb : ∀ j, 0 ≤ lb j)
    (K : Matrix (α × Fin 2) (β × Fin 2) ℝ)
    (h17 : williamson la * K + K * williamson lb = 0) (i : α) (j : β) :
    la i • K.submatrix (fun x => (i, x)) (fun y => (j, y)) =
        lb j • (J2 * K.submatrix (fun x => (i, x)) (fun y => (j, y)) * J2) ∧
      (la i ≠ lb j → K.submatrix (fun x => (i, x)) (fun y => (j, y)) = 0) := by sorry

end FermionModewise
