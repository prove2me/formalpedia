-- Prove2me | Theorems.Thm_AronszajnRK_SubspaceSum_complement_product_vanishes
-- name    : AronszajnRK.SubspaceSum.complement_product_vanishes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:12:55.203992+00:00
-- url     : https://prove2.me/theorems/f9600b6c-1605-4320-a3aa-b266e5574501
-- title:
--   §12, p. 377 — complementary projection product tends strongly to zero
-- statement:
--   Let $F_1,F_2$ be closed subspaces of a complex Hilbert space. Let $P$ project onto $\overline{F_1+F_2}$, and let $P_i$ project onto $F_i$. For every vector $f$,
--
--   $$
--   [(P-P_1)(P-P_2)]^m f\longrightarrow0\qquad(m\to\infty).
--   $$
--
--   This disposes of the remaining power in the finite projection identity.
--
--   **Formalization Note** The paragraph on p. 377 omits the brackets around the product once and prints $P\ominus P_2$ where the surrounding formulas require $P-P_2$. This statement follows the bracketed expression of Eqs. (1) and (4). Convergence is in vector norm.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 377, §12, paragraph before Eq. (7)

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, p. 377 (PDF p. 41). The product of the two complementary projections
converges strongly to zero. We use the bracketed power of Eq. (1); the
unbracketed expression in the running text is a misprint. -/
theorem complement_product_vanishes {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto (fun m : ℕ => (((P - P₁) * (P - P₂)) ^ m) f)
      Filter.atTop (nhds 0) := by sorry

end AronszajnRK.SubspaceSum
