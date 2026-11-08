-- Prove2me | Theorems.Thm_AffDisp4n_exchange_matrix_invertible
-- name    : AffDisp4n.exchange_matrix_invertible
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:33.30942+00:00
-- url     : https://prove2.me/theorems/78b8c8e3-ee65-4336-bc1e-5bd7f959f09e
-- title:
--   §2.6, p.19 (Preserving the representation) — the exchange (AR) keeps the auxiliary matrix invertible
-- statement:
--   Let $A \in \mathbb F_2^{r \times r}$ be invertible, let $\nu \in \mathbb F_2^r$, and let $j$ be an index with $(A^{-1} \nu)_j = 1$. Then the matrix $A'$ obtained from $A$ by replacing its $j$-th column with $\nu$ is invertible:
--   $$
--   \det A' \ne 0 .
--   $$
--
--   In the exchange (AR), $\nu = N_x$ is the column of the parameter $x$ in $N$ and $j$ is the column of the auxiliary variable $Q$. The hypothesis says that $Q$ depends on $x$. The lemma keeps the fairness condition after the exchange.
--
--   Differences from the source:
--   - generalization: ν = Nₓ, the column of the parameter x in the parameter matrix N → an arbitrary vector ν ∈ 𝔽₂ʳ; reason: the argument (A′ = AB, det B = tⱼ) uses nothing about ν except (A⁻¹ν)ⱼ = 1; taking ν = Nₓ gives the paper's statement
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, p.19, paragraph "Preserving the representation"

import Mathlib

namespace AffDisp4n

/-- **The auxiliary matrix stays invertible under the exchange (AR)** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6 "Preserving the
representation", p.19): "let j be the column index of Q, let Nₓ be the column of x in N, and let
t = A⁻¹Nₓ … Since A′ is obtained from A by replacing its jth column with Nₓ, we have A′ = AB, where B is
the identity matrix with its jth column replaced by t. As det B = tⱼ = 1, the matrix A′ is invertible."
Over `𝔽₂`: if `A` is invertible and `(A⁻¹ ν)ⱼ = 1`, then `A` with its `j`th column replaced by `ν` is
invertible. -/
theorem exchange_matrix_invertible {r : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod 2)) (hA : IsUnit A.det)
    (ν : Fin r → ZMod 2) (j : Fin r) (hj : (A⁻¹.mulVec ν) j = 1) :
    IsUnit (A.updateCol j ν).det := by sorry

end AffDisp4n
