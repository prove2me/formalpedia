-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_2_1
-- name    : EzeunalaJiangKS.Signing.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:01:07.288257+00:00
-- url     : https://prove2.me/theorems/121a82d4-5e81-4e50-9eb5-da5df0aa43b1
-- title:
--   Lemma 2.1 — Subspace covariance
-- statement:
--   Let $L$ be a linear subspace of $\mathbb R^m$ of dimension $\ell$, and let $\kappa>1$. There is a real positive semidefinite matrix $U$ such that
--   $$\operatorname{range}(U)\subseteq L,\qquad U_{ii}\le1\ (i\in[m]),\qquad U\preceq\kappa\operatorname{diag}(U),\qquad\operatorname{Tr}U\ge\ell-m/\kappa.$$
--   Zero ambient dimension and the zero subspace are allowed; the lower trace bound may be nonpositive. This is the general subspace covariance statement used later, with no restriction to the particular value of $\kappa$ in the application.
--
--   Differences from the source:
--   - encoding: L has dimension ell in R^m → L is a real submodule of Fin m -> real and ell is its computed finrank; range containment is forall v, U v belongs to L; reason: these are the finite-dimensional definitions of subspace, dimension and range; m=0 is retained
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 2.1, printed p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_MatrixData

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 2.1, printed p.3 / PDF p.4, including zero ambient dimension. -/
theorem lemma_2_1 (m : ℕ) (L : Submodule ℝ (Fin m → ℝ)) (κ : ℝ) (hκ : 1 < κ) :
  ∃ U : RMat m, U.PosSemidef ∧
    (∀ v : Fin m → ℝ, U.mulVec v ∈ L) ∧ (∀ i, U i i ≤ 1) ∧
    (κ • Matrix.diagonal (fun i => U i i) - U).PosSemidef ∧
    (Module.finrank ℝ L : ℝ) - (m : ℝ) / κ ≤ U.trace := by sorry

end EzeunalaJiangKS.Signing
