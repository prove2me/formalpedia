-- Prove2me | Theorems.Thm_FRouting_fact_3_4
-- name    : FRouting.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:35.376081+00:00
-- url     : https://prove2.me/theorems/db2eae45-f7df-448c-9038-8de1f43f24dc
-- title:
--   Fact 3.4 — $\langle\Phi|A\otimes B|\Phi\rangle$
-- statement:
--   For any two $d\times d$ matrices $A,B$,
--   $$\langle\Phi|(A\otimes B)|\Phi\rangle=\frac1d\sum_{i,j}\langle i|A|j\rangle\langle i|B|j\rangle=\frac1d\sum_{i,j}A_{ij}(B^T)_{ji}=\frac1d\operatorname{tr}(AB^T).$$
--
--   This evaluates the EPR test on a product state.
--
--   Differences from the source:
--   - encoding: d left unbounded in §3.1 → any natural d; reason: d = 0 only gives 0 = 0, and no instance of the paper changes
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Fact 3.4, p.14

import Definitions.Def_FRouting_Phi

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace FRouting

/-- **Fact 3.4.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Fact 3.4, p.14: "For any two operators A, B:
⟨Φ| (A ⊗ B) |Φ⟩ = (1/d) ∑_{i,j} ⟨i|A|j⟩⟨i|B|j⟩ = (1/d) ∑_{i,j} A_{ij} (Bᵀ)_{ji} = (1/d) tr(A Bᵀ)."

All three equalities of the display are stated. -/
theorem fact_3_4 (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    star (phiVec d) ⬝ᵥ ((A ⊗ₖ B) *ᵥ phiVec d) = (1 / (d : ℂ)) * ∑ i, ∑ j, A i j * B i j ∧
    (1 / (d : ℂ)) * ∑ i, ∑ j, A i j * B i j = (1 / (d : ℂ)) * ∑ i, ∑ j, A i j * Bᵀ j i ∧
    (1 / (d : ℂ)) * ∑ i, ∑ j, A i j * Bᵀ j i = (1 / (d : ℂ)) * (A * Bᵀ).trace := by sorry

end FRouting
