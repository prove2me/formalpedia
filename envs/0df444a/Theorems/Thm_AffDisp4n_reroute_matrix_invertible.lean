-- Prove2me | Theorems.Thm_AffDisp4n_reroute_matrix_invertible
-- name    : AffDisp4n.reroute_matrix_invertible
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:32.063759+00:00
-- url     : https://prove2.me/theorems/b8e29dd4-ef0a-4c65-86d7-5e94e396cb72
-- title:
--   §2.6, p.19 (Preserving the representation) — deleting a row and a column through a single nonzero entry keeps the auxiliary matrix invertible
-- statement:
--   Let $A$ be an invertible $(r+1) \times (r+1)$ matrix over $\mathbb F_2$ whose $k$-th column has its only nonzero entry in row $i$. Then the $r \times r$ matrix obtained from $A$ by deleting row $i$ and column $k$ is invertible.
--
--   This is the last step of the paper's argument that rerouting an auxiliary variable $v = U + c_0$, or deleting an auxiliary variable used in a single equation, preserves fairness. After the substitution, the column of $v$ has a single nonzero entry, in the row of its equation.
--
--   Differences from the source:
--   - generalization: the auxiliary matrix after substituting v = U + c₀ in every equation, whose kth column has a single nonzero entry in row i → any invertible (r+1)×(r+1) matrix over 𝔽₂ whose column k vanishes outside row i; reason: the determinant expansion uses only these properties; the paper's matrix is an instance
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, p.19, paragraph "Preserving the representation"

import Mathlib

namespace AffDisp4n

/-- **The auxiliary matrix stays invertible under rerouting and deletion** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6 "Preserving the
representation", p.19): "the kth column of A has a single nonzero entry in row i. Expanding the
determinant along this column, we see that deleting row i and column k from A leaves a matrix whose
determinant equals det A up to sign. Hence, the auxiliary matrix of the new system is invertible."
Over `𝔽₂`: if `A` is an invertible `(r+1) × (r+1)` matrix whose column `k` vanishes outside row `i`, then
deleting row `i` and column `k` leaves an invertible matrix. -/
theorem reroute_matrix_invertible {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod 2))
    (hA : IsUnit A.det) (i k : Fin (r + 1)) (hcol : ∀ i' : Fin (r + 1), i' ≠ i → A i' k = 0) :
    IsUnit (A.submatrix i.succAbove k.succAbove).det := by sorry

end AffDisp4n
