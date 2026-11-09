-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_lemma_3_1
-- name    : ExplicitTensorBarrier694.Explicit.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:42.471038+00:00
-- url     : https://prove2.me/theorems/90f2895a-6a55-4172-b3ef-329256375c8d
-- title:
--   Lemma 3.1 — invertible central Koszul matrix in general position
-- statement:
--   Let $e\ge2$, $s=2e-1$, and let $z_1,\ldots,z_s$ be any basis of a complex $s$-dimensional space. Let $b_1,\ldots,b_s$ and $c_1,\ldots,c_s$ be collections in complex spaces of dimension $e$. Assume separately that every $e$-subset of each collection is linearly independent. Then
--
--   $$K_{e-1}\!\left(\sum_{\ell=1}^{s}z_\ell\otimes b_\ell\otimes c_\ell\right)\text{ is invertible}.$$
--
--   The conclusion is bijectivity of the central Koszul linear map; its domain and codomain have the same dimension. This is the nondegeneracy criterion used for the polynomial family, without assuming determinant nonvanishing as input.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex mode spaces → coordinate spaces with arbitrary natural dimensions; reason: choosing bases identifies every source instance with one of these arrays; tensors, dual subspaces, and Koszul maps are transported by those bases
--   - encoding: indices 1 through s for polynomial and basis labels → Fin s for these labels; reason: a bijective relabeling; zero-based block indices and all powers are unchanged
--   - encoding: invertible Koszul matrix → bijective linear map between the column and row coordinate spaces; reason: the central matrix is square in dimension; the two exterior basis types need not be definitionally equal
--   - encoding: Koszul flattening K_p as an abstract linear map → its matrix in increasing exterior bases z_I and the standard bases of B* and C, with sign (−1)^#{i∈I : i<l} for z_l∧z_I; reason: this is the matrix of the source map in those bases, and rank, kernel dimension and invertibility do not depend on the bases
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.1 and Section 3 preamble, p.7 (PDF p.7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.1, p.7.
Standing assumption e≥2, s=2e−1, arbitrary basis and both general-position conditions. -/
theorem lemma_3_1 (e : ℕ) (he : 2 ≤ e)
    (z : Module.Basis (Fin (2 * e - 1)) ℂ (Fin (2 * e - 1) → ℂ))
    (b c : Fin (2 * e - 1) → Fin e → ℂ)
    (hb : GeneralPosition b) (hc : GeneralPosition c) :
    KoszulInvertible (e - 1) (generalPositionTensor z b c) := by sorry

end ExplicitTensorBarrier694.Explicit
