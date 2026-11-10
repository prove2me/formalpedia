-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_claim_4_1
-- name    : EzeunalaJiangKS.Signing.claim_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:05:37.734767+00:00
-- url     : https://prove2.me/theorems/d2903610-55b7-474f-b6e4-bfa33a8b7ad2
-- title:
--   Claim 4.1 — Inverse of the linearized constraints
-- statement:
--   At any normalized data and cube state, form $L$ and $\mathcal T$ from the actual chosen optimizer $(t,X,Y)$. The map $L$ on Hermitian pairs is invertible, and for every Hermitian pair $(F,G)$ the following series converges to its inverse image:
--   $$L^{-1}(F,G)=\sum_{j=0}^\infty\mathcal T^j(XFX,YGY).$$
--   The inverse sends positive semidefinite pairs to positive semidefinite pairs, and in the Frobenius pair geometry,
--   $$\|L^{-1}\|\le\varepsilon^{-1},\qquad\|L\|\le4K^2+c\nu,\qquad K=100,\ c=40.$$
--   Invertibility is expressed as a unique Hermitian preimage of every Hermitian pair. Each norm inequality is expressed by the equivalent bound on every Hermitian input pair. The series assertion is actual convergence, excluding the nonsummable-series default. This is the source-specific linearization used by the variation definitions.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - encoding: invertible L, convergent inverse series, Frobenius operator norm bounds → unique Hermitian preimages, HasSum, and pointwise homogeneous Frobenius norm bounds; reason: these are equivalent formulations of invertibility, convergence and the two operator norm bounds; the finite-dimensional matrix topology agrees with Frobenius topology
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Claim 4.1, printed p. 9 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Linearization
import Definitions.Def_EzeunalaJiangKS_Signing_FaceCalculus

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Claim 4.1, printed p.9 / PDF p.10. Norm bounds expressed as the equivalent bounds on every vector. -/
theorem claim_4_1 (N d : ℕ) (A : Fin N → CMat d) (x₀ x : State N)
    (hA : normalized A x₀) (hx : cube x) :
  let X := (optimizer A x₀ x).2.1
  let Y := (optimizer A x₀ x).2.2
  (∀ F : PairMat d, hermitianPair F →
    (∃! Z : PairMat d, hermitianPair Z ∧ linearized A x X Y Z = F) ∧
    HasSum (fun j : ℕ => (feedback A x X Y)^[j] (X * F.1 * X, Y * F.2 * Y))
      (linearizedInverse A x X Y F)) ∧
  (∀ F : PairMat d, positivePair F → positivePair (linearizedInverse A x X Y F)) ∧
  (∀ F : PairMat d, hermitianPair F →
    frobeniusPair (linearizedInverse A x X Y F) ≤ (epsilon A)⁻¹ * frobeniusPair F ∧
    frobeniusPair (linearized A x X Y F) ≤
      (4 * (100 : ℝ)^2 + couplingConstant * variance A) * frobeniusPair F) := by sorry

end EzeunalaJiangKS.Signing
