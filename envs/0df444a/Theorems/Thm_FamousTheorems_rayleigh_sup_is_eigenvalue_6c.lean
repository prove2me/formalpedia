-- Prove2me | Theorems.Thm_FamousTheorems_rayleigh_sup_is_eigenvalue_6c
-- name    : FamousTheorems.rayleigh_sup_is_eigenvalue_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:33.711217+00:00
-- url     : https://prove2.me/theorems/ec2947b1-58e2-44f4-9452-888e2f47c750
-- title:
--   Rayleigh's principle: the maximum of the Rayleigh quotient is an eigenvalue
-- statement:
--   **Rayleigh's principle.** Let $T$ be a self-adjoint operator on a nonzero finite-dimensional real or complex inner product space $E$. Then the supremum of the Rayleigh quotient
--   $$\sup_{x\ne0}\frac{\operatorname{Re}\langle Tx,x\rangle}{\|x\|^2}$$
--   is an eigenvalue of $T$.
--
--   This supremum is therefore the largest eigenvalue of $T$. It is the first step of the Courant–Fischer min-max characterisation of eigenvalues, and it gives a variational proof of the spectral theorem: restrict to the orthogonal complement of the eigenvector and repeat.
--
--   **Formalization note.** Mathlib's `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`, over any `RCLike` field $\mathbb K$ ($\mathbb R$ or $\mathbb C$). Self-adjointness is `T.IsSymmetric`, i.e. $\langle Tx,y\rangle=\langle x,Ty\rangle$. The supremum is a real number, cast to $\mathbb K$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rayleigh_sup_is_eigenvalue_6c {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [Nontrivial E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    Module.End.HasEigenvalue T
      ((⨆ x : { x : E // x ≠ 0 }, RCLike.re (inner 𝕜 (T x) (x : E)) / ‖(x : E)‖ ^ 2 : ℝ) : 𝕜) := by sorry

end FamousTheorems
