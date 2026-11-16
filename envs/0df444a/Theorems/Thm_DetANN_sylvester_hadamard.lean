-- Prove2me | Theorems.Thm_DetANN_sylvester_hadamard
-- name    : DetANN.sylvester_hadamard
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T17:41:21.837975+00:00
-- url     : https://prove2.me/theorems/798d3dbf-870b-4fa3-ba72-b207ab98ba83
-- title:
--   The Sylvester–Hadamard matrix and its butterfly identity
-- statement:
--   Let $H_k$ be the Sylvester–Hadamard matrix on $\mathrm{Fin}(2^k)$, $(H_k)_{jr}=(-1)^{\langle j,r\rangle}$ (definition `DetANN_Sylvester`). Then:
--
--   1. every entry of $H_k$ is $\pm1$;
--   2. $H_k^{\mathsf T}H_k=2^k I$;
--   3. for $z\in\mathbb R^{2^{k+1}}$ with lower half $z'$ and upper half $z''$,
--   $$H_{k+1}\begin{pmatrix}z'\\ z''\end{pmatrix}=\begin{pmatrix}H_k(z'+z'')\\ H_k(z'-z'')\end{pmatrix}.$$
--
--   Items 1 and 2 are the hypotheses on the matrix in the block theorems of §6. The butterfly identity 3 evaluates $H_kz$ with $k2^k$ additions, the $O(d\log d)$ evaluation behind the query bound of Theorem 1.1.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.1, p.14 (the Walsh–Hadamard matrix and multiplication by H)

import Mathlib
import Definitions.Def_DetANN_Sylvester

namespace DetANN

/-- **The Sylvester–Hadamard matrix** (§6.1). `H_k` has entries `±1`, satisfies `H_kᵀ H_k = 2^k I`,
and obeys the butterfly identity `H_{k+1}(z', z'') = (H_k(z' + z''), H_k(z' − z''))`, where `z'` and
`z''` are the lower and upper halves of `z ∈ ℝ^{2^{k+1}}`. -/
theorem sylvester_hadamard (k : ℕ) :
    (∀ j r, sylvester k j r = 1 ∨ sylvester k j r = -1) ∧
    (sylvester k).transpose * sylvester k =
      ((2 ^ k : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) ∧
    ∀ (z : Fin (2 ^ (k + 1)) → ℝ) (i : Fin (2 ^ k)),
      (sylvester (k + 1)).mulVec z (loIdx k i) =
          (sylvester k).mulVec (fun r => z (loIdx k r) + z (hiIdx k r)) i ∧
      (sylvester (k + 1)).mulVec z (hiIdx k i) =
          (sylvester k).mulVec (fun r => z (loIdx k r) - z (hiIdx k r)) i := by sorry

end DetANN
