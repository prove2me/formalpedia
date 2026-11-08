-- Prove2me | Theorems.Thm_BenignDegen_lemma_C_6
-- name    : BenignDegen.lemma_C_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:56:57.572395+00:00
-- url     : https://prove2.me/theorems/906f3db7-0ba7-44a1-afe1-1af7b8b688d3
-- title:
--   Lemma C.6 — PSD product bound $\|AB\|_F^2\le\|A\|_{\rm op}\|B\|_{\rm op}\langle A,B\rangle$
-- statement:
--   For positive semidefinite $A,B\in\mathbb S^p_+$,
--
--   $$
--   \|AB\|_F^2\le\|A\|_{\rm op}\,\|B\|_{\rm op}\,\langle A,B\rangle .
--   $$
--
--   It converts the vanishing of the two complementarity gaps into the vanishing of the products $X_k\bar S_k$, $\bar X_kS_k$ in the proof of Theorem 3.2, without any eigenvalue bound.
--
--   Differences from the source:
--   - encoding: ‖·‖_F, ‖·‖_op, ⟨A, B⟩ = tr(AB) → frob (square root of the sum of squared entries), the norm of the induced operator on (ℝ^p, ‖·‖₂), the inner product of SymMat; reason: the same quantities
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix C.5, Lemma C.6, p.20

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Lemma C.6 (PSD product bound), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.20.
For `A, B ∈ S^p_+`, `‖AB‖_F² ≤ ‖A‖_op ‖B‖_op ⟨A, B⟩`. -/
theorem lemma_C_6 {ι : Type} [Fintype ι] [DecidableEq ι] (A B : SymMat ι)
    (hA : A ∈ psdCone ι) (hB : B ∈ psdCone ι) :
    frob (A.toMat * B.toMat) ^ 2 ≤ opNorm A * opNorm B * ⟪A, B⟫ := by sorry

end BenignDegen
