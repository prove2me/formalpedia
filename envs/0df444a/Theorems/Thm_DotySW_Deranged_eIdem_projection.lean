-- Prove2me | Theorems.Thm_DotySW_Deranged_eIdem_projection
-- name    : DotySW.Deranged.eIdem_projection
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:26.371312+00:00
-- url     : https://prove2.me/theorems/0ead686c-c823-4b6a-90cd-3bceb5ae860c
-- title:
--   §4.2 — $e$ is the idempotent of the projection onto $\mathfrak{sl}_n^{\otimes r}$
-- statement:
--   Let $n\ne0$ and $e=\prod_i(1-n^{-1}c_{i,-i})$. Then
--
--   1. $e^2=e$ in $\mathcal B^{(n)}_{r,r}$;
--   2. the image of $\sigma(e)$ on $V^{r,r}$ is $\mathfrak{sl}_n^{\otimes r}$;
--   3. $\sigma(e)$ vanishes on every other summand $M_S$, $S\ne\{1,\dots,r\}$, of the decomposition of $\mathfrak{gl}_n^{\otimes r}$.
--
--   So $\sigma(e)$ is the projection onto the summand $\mathfrak{sl}_n^{\otimes r}$, which lets §4.2 pass from $V^{r,r}$ to $\mathfrak{sl}_n^{\otimes r}$.
--
--   Differences from the source:
--   - generalization: $e$ considered in a sentence with the hypothesis $n\ge2r$ → the hypothesis n ≠ 0; reason: the formula for e only needs n invertible, and n ≥ 2r with r ≥ 1 implies n ≠ 0; for r = 0 the element e is 1 in the source and here
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, unnumbered, p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_sigma
import Definitions.Def_DotySW_Deranged_eIdem
import Definitions.Def_DotySW_Deranged_slTensor
import Definitions.Def_DotySW_Deranged_slotSplit

namespace DotySW.Deranged

/-- **`e` is the idempotent of the projection onto the summand `sl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, unnumbered, p. 11.

`e` is idempotent in `B^{(n)}_{r,r}`, the image of `σ(e)` is `sl_n^{⊗r}`, and `σ(e)` kills every other
summand of the decomposition of `gl_n^{⊗r}`.

**Formalization Note** Stated for `n ≠ 0`, which is what the formula for `e` needs; the paper mentions
`e` in a sentence under `n ≥ 2r`. -/
theorem eIdem_projection (n r : ℕ) (hn : n ≠ 0) :
    IsIdempotentElem (eIdem n r) ∧
    LinearMap.range (Matrix.mulVecLin (sigma n r r (eIdem n r))) = slTensor n r ∧
    ∀ S : Finset (Fin r), S ≠ Finset.univ → ∀ w ∈ slotSplit n r S,
      (sigma n r r (eIdem n r)).mulVec w = 0 := by sorry

end DotySW.Deranged
