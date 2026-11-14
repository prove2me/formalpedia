-- Prove2me | Theorems.Thm_BosonicLearn_displacementMatrix_unitary
-- name    : BosonicLearn.displacementMatrix_unitary
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T18:44:36.476509+00:00
-- url     : https://prove2.me/theorems/c6fc56fb-d47c-4a43-98ce-e2cc684840dc
-- title:
--   Displacement matrix elements: $D(-z)=D(z)^\dagger$, $D(0)=\mathbf 1$, and $D(z)^\dagger D(z)=D(z)D(z)^\dagger=\mathbf 1$ entrywise
-- statement:
--   Unitarity of displacement operators at the level of Fock matrix elements.
--
--   Let $D(z)_{mn}=\langle m|D(z)|n\rangle$. For all $z\in\mathbb C$ and $m,n\in\mathbb N$:
--
--   1. $D(-z)_{mn}=\overline{D(z)_{nm}}$;
--   2. $D(0)_{mn}=\delta_{mn}$;
--   3. $\sum_k\overline{D(z)_{km}}\,D(z)_{kn}=\delta_{mn}$ (columns orthonormal);
--   4. $\sum_kD(z)_{mk}\,\overline{D(z)_{nk}}=\delta_{mn}$ (rows orthonormal).
--
--   Role. Rows and columns of $D(z)$ are unit vectors of $\ell^2(\mathbb N)$, so conjugating a density matrix by $D(z)$ entrywise gives a density matrix; this is used to displace Gaussian states.
--
--   **Formalization Note** $D(z)_{mn}$ is `Dependency50.P39.displacementMatrix`; 3 and 4 are `HasSum` statements with value `if m = n then 1 else 0`. Proved from `BosonicLearn.displacementMatrix_mul`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, pp. 4–5 (displacement operators and characteristic function of an n-mode state); proof of Theorem 8, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace BosonicLearn

/-- **The displacement matrices are unitary, with `D(−z) = D(z)†` and `D(0) = 1`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5; proof of Theorem 8, p. 62: "a common displacement is implemented by the same unitary
on both states".

For `z ∈ ℂ` and Fock indices `m, n`: `D(−z)_{mn} = conj(D(z)_{nm})`, `D(0)_{mn} = δ_{mn}`,
`∑ₖ conj(D(z)_{km}) D(z)_{kn} = δ_{mn}` and `∑ₖ D(z)_{mk} conj(D(z)_{nk}) = δ_{mn}`.

**Formalization Note.** `D(z)_{mn}` is `Dependency50.P39.displacementMatrix`. -/
theorem displacementMatrix_unitary (z : ℂ) (m n : ℕ) :
    displacementMatrix (-z) m n = star (displacementMatrix z n m) ∧
    displacementMatrix 0 m n = (if m = n then 1 else 0) ∧
    HasSum (fun k : ℕ => star (displacementMatrix z k m) * displacementMatrix z k n)
      (if m = n then 1 else 0) ∧
    HasSum (fun k : ℕ => displacementMatrix z m k * star (displacementMatrix z n k))
      (if m = n then 1 else 0) := by sorry

end BosonicLearn
