-- Prove2me | Theorems.Thm_EastinKnill_Transversal_local_hermitian_scalar
-- name    : EastinKnill.Transversal.local_hermitian_scalar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:46.332714+00:00
-- url     : https://prove2.me/theorems/134db97a-1c4e-4243-b112-3dea549ed6a4
-- title:
--   Proof of Theorem 1, p. 3 — for a local-error-detecting code, a logical sum of local Hermitians acts as a scalar: $DP \propto P$
-- statement:
--   Let $P$ be the projector of a local-error-detecting code on a composite system: $P(I\otimes E\otimes I)P \propto P$ for every operator $E$ on any single subsystem. Let $H_j$ be Hermitian operators on the subsystems and $D = \sum_j I\otimes H_j\otimes I$, and assume $D$ preserves the code space, $(I-P)DP = 0$. Then there is a scalar $c$ with
--
--   $$D\,P = c\,P.$$
--
--   In the proof of Theorem 1 this is the step $DP = PDP = \sum_j \alpha_j P H_j P \propto P$: the Lie algebra of the identity component acts on the code space by scalars.
--
--   **Formalization Note** The real coefficients $\alpha_j$ of the page are absorbed into $H_j$. The Hermiticity hypothesis on $H_j$ is kept as on the page, though local error detection covers every $E$.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Theorem 1, displays "PH_jP ∝ P" and "DP = PDP = … ∝ P"

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem local_hermitian_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hP : IsCodeProjector P)
    (hdet : IsLocalErrorDetecting P) (H : ∀ j, Matrix (α j) (α j) ℂ)
    (hH : ∀ j, (H j).IsHermitian)
    (hlog : (1 - P) * (∑ j, localOp α j (H j)) * P = 0) :
    ∃ c : ℂ, (∑ j, localOp α j (H j)) * P = c • P := by sorry

end EastinKnill.Transversal
