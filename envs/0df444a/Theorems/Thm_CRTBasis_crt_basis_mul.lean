-- Prove2me | Theorems.Thm_CRTBasis_crt_basis_mul
-- name    : CRTBasis.crt_basis_mul
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T22:27:54.303303+00:00
-- url     : https://prove2.me/theorems/52157241-e3dd-442b-aed9-d1dd9581638c
-- title:
--   PR #6453: the composite matrix equals multiplication in the CRT basis
-- statement:
--   In the CRT basis, the composite of two multiplications is multiplication, and its matrix is the diagonal of the product.
--
--   Let $K$ be a field and $R = \prod_{i \in \iota} K$ a product of copies of it — the image of a ring under the Chinese remainder theorem for coprime moduli. Multiplication by a vector $x \in R$ is the $K$-linear map $y \mapsto x\,y$. In the standard basis of $R$ its matrix is the diagonal matrix $\mathrm{diag}(x)$, so the composite of multiplication by $x$ with multiplication by $y$ has matrix $\mathrm{diag}(x)\,\mathrm{diag}(y) = \mathrm{diag}(x y)$: the composite matrix is multiplication, coordinatewise.
--
--   This is the algebraic content of the module identity the construction's word realises, in the basis the CRT supplies.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block).

import Definitions.Def_Pr6453_CRT

set_option autoImplicit false

namespace CRTBasis

theorem crt_basis_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] (x y : ι → K) :
    LinearMap.toMatrix' ((mulLin x).comp (mulLin y)) = Matrix.diagonal (x * y) ∧
      (LinearMap.toMatrix' (mulLin x)) * (LinearMap.toMatrix' (mulLin y)) =
        Matrix.diagonal (x * y) := by
  sorry

end CRTBasis
