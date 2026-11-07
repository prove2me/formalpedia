-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_eq_3_13
-- name    : ArgmaxDeFinetti.eq_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:51.082564+00:00
-- url     : https://prove2.me/theorems/e3275111-fffb-4063-878c-d00df72eb9a0
-- title:
--   Eq. (3.13) — Takagi decomposition $Z=U\Sigma U^{\mathsf T}$
-- statement:
--   Let $Z$ be an $m\times m$ complex matrix with $Z^{\mathsf T}=Z$. Then
--   $$
--   Z=U\Sigma U^{\mathsf T},
--   $$
--   where $U$ is unitary and $\Sigma$ is diagonal with nonnegative entries, and the diagonal entries of $\Sigma$ are the singular values of $Z$ (counted with multiplicity).
--
--   This symmetric form of the singular-value decomposition identifies the tensor norms of symmetric two-tensors with Schatten norms (Fact 3.4).
--
--   Differences from the source:
--   - encoding: an m × m matrix (m = dim H) → a matrix indexed by a finite type ι; reason: relabelling the index set
--   - encoding: the diagonal entries of Σ are the singular values of Z → the multiset {s_i} equals the multiset of singular values √λ_j(Z†Z); reason: the same claim, with multiplicities
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.3, p.25, eq. (3.13)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_opNormS

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Takagi decomposition, eq. (3.13)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.3, p.25. A complex symmetric matrix `Z = Zᵀ` factors as
`Z = U Σ Uᵀ` with `U` unitary and `Σ` diagonal with nonnegative entries, and the diagonal entries of `Σ` are the
singular values of `Z`.

**Formalization Note** The `m × m` matrix is indexed by a finite type `ι` (`m = |ι|`). "The diagonal entries of
`Σ` are the singular values of `Z`" is the equality of multisets `{s_i} = {s_j(Z)}` (with multiplicity), the
singular values being `√λ_j(Z†Z)` (`singularValues`). -/
theorem eq_3_13 {ι : Type} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℂ) (hZ : Zᵀ = Z) :
    ∃ U ∈ Matrix.unitaryGroup ι ℂ, ∃ s : ι → ℝ, (∀ i, 0 ≤ s i) ∧
      Z = U * Matrix.diagonal (fun i => (s i : ℂ)) * Uᵀ ∧
      Multiset.map s Finset.univ.val = Multiset.map (singularValues Z) Finset.univ.val := by sorry

end ArgmaxDeFinetti
