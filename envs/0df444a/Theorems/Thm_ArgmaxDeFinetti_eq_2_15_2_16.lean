-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_eq_2_15_2_16
-- name    : ArgmaxDeFinetti.eq_2_15_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:16.393715+00:00
-- url     : https://prove2.me/theorems/752fd6ca-ac2a-4d3d-9ff9-b78f80d8bd8b
-- title:
--   Eqs. (2.15)–(2.16) — tensor norms as Schatten norms of the coefficient matrix
-- statement:
--   Let $\mathcal X$, $\mathcal Y$ be finite-dimensional Hilbert spaces, $z\in\mathcal X\otimes\mathcal Y$, and $Z$ its coefficient matrix in orthonormal bases. Then
--   $$
--   \|z\|_\varepsilon=\|Z\|_\infty,\qquad \|z\|=\|Z\|_2,\qquad \|z\|_\pi=\|Z\|_1,
--   $$
--   and, writing $\operatorname{Schmidt-rank}(z)$ for the number of nonzero Schmidt coefficients of $z$, for every $w\in\mathcal X\otimes\mathcal Y$,
--   $$
--   |\langle z,w\rangle|\le\|z\|_\pi\,\|w\|_\varepsilon,\qquad \|z\|_\pi\le\sqrt{\operatorname{Schmidt-rank}(z)}\,\|z\| .
--   $$
--   These identities transfer the tensor-norm estimates of the argmax analysis to matrix Schatten norms.
--
--   Differences from the source:
--   - encoding: X, Y with chosen orthonormal bases → ℂ^ι, ℂ^κ with their standard bases, Z = coeffMat z; reason: every such pair is isometric to coordinate spaces
--   - encoding: Schmidt-rank(z), the number of nonzero Schmidt coefficients → the rank of the coefficient matrix Z; reason: the Schmidt coefficients are the nonzero singular values of Z
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.22, eqs. (2.15)–(2.16)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_opNormS
import Definitions.Def_WildeQIT_hsNorm
import Definitions.Def_ArgmaxDeFinetti_injNorm
import Definitions.Def_ArgmaxDeFinetti_projNorm
import Definitions.Def_ArgmaxDeFinetti_coeffMat

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Tensor norms as Schatten norms, eqs. (2.15)–(2.16)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.22. For `z ∈ X ⊗ Y` with coefficient
matrix `Z`, `∥z∥_ε = ∥Z∥_∞`, `∥z∥ = ∥Z∥₂`, `∥z∥_π = ∥Z∥₁` (2.15); and for every `w ∈ X ⊗ Y`,
`|⟨z, w⟩| ≤ ∥z∥_π ∥w∥_ε` and `∥z∥_π ≤ √(Schmidt-rank(z)) ∥z∥` (2.16).

**Formalization Note** `X = ℂ^ι`, `Y = ℂ^κ` with their standard orthonormal bases; `Z = coeffMat z`. The Schmidt rank
(number of nonzero Schmidt coefficients) is the rank of `Z`. `∥z∥` is the Euclidean norm `vnorm`. -/
theorem eq_2_15_2_16 {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (z : ι × κ → ℂ) :
    injNorm z = opNormS (coeffMat z) ∧
    vnorm z = WildeQIT.hsNorm (coeffMat z) ∧
    projNorm z = WildeQIT.traceNorm (coeffMat z) ∧
    (∀ w : ι × κ → ℂ, ‖vinner z w‖ ≤ projNorm z * injNorm w) ∧
    projNorm z ≤ Real.sqrt ((coeffMat z).rank : ℝ) * vnorm z := by sorry

end ArgmaxDeFinetti
