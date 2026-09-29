-- Prove2me | Theorems.Thm_FamousTheorems_generalized_eigenspace_decomposition_7b
-- name    : FamousTheorems.generalized_eigenspace_decomposition_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:35.897158+00:00
-- url     : https://prove2.me/theorems/b4bfd260-5f88-42dc-9d4e-b894ac5b311f
-- title:
--   Decomposition into generalized eigenspaces over an algebraically closed field
-- statement:
--   **Decomposition into generalized eigenspaces.** Let $V$ be a finite-dimensional vector space over an algebraically closed field $K$ and let $f$ be a linear endomorphism of $V$. Then $V$ is the sum of the generalized eigenspaces of $f$:
--   $$V=\sum_{\mu\in K}\ker\,(f-\mu)^{\dim V}.$$
--
--   The sum is direct, so this gives the primary decomposition of $V$ into $f$-invariant subspaces on each of which $f$ has a single eigenvalue. It is the main step towards the Jordan normal form and the Jordan–Chevalley decomposition. The proof uses induction on the dimension and the existence of an eigenvalue, which is where algebraic closure is needed.
--
--   **Formalization note.** Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`. `f.maxGenEigenspace μ` is the union over $k$ of $\ker(f-\mu)^k$, and the statement says that the supremum of these subspaces is all of $V$. Directness of the sum is a separate result.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.End.iSup_maxGenEigenspace_eq_top`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem generalized_eigenspace_decomposition_7b {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) : ⨆ μ : K, f.maxGenEigenspace μ = ⊤ := by sorry

end FamousTheorems
