-- Prove2me | Theorems.Thm_CurveSymmetry_genus_congr
-- name    : CurveSymmetry.genus_congr
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:40:57.717694+00:00
-- url     : https://prove2.me/theorems/c7ad6fde-7da4-466e-ae68-4b59ebd0e58d
-- title:
--   The genus of a field over $\mathbb C$ is invariant under isomorphisms of $\mathbb C$-algebras
-- statement:
--   For a field $K$ containing $\mathbb C$, let $\Omega_{K/\mathbb C}$ be its module of Kähler differentials, with universal derivation $d$. A *place* of $K$ is a valuation ring $\mathcal O\ne K$ of $K$ (a subring with $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K$) that contains $\mathbb C$. A differential is *regular at* $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $a\,db$ with $a,b\in\mathcal O$. The *holomorphic differentials* $H(K)\subseteq\Omega_{K/\mathbb C}$ are those regular at every place of $K$, and the *genus* of $K$ is $g(K)=\dim_{\mathbb C}H(K)$.
--
--   Let $K$ and $L$ be fields containing $\mathbb C$, and suppose there is an isomorphism of $\mathbb C$-algebras $K\cong L$. Then
--
--   $$g(K)=g(L).$$
--
--   So the genus depends only on the field, not on a plane model. It transfers the genus computed on the double cover of the family to the function field of the curve $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)=0$ (Lemma 4), and in Remark 5 it is applied to the isomorphism of function fields that a similarity between $\operatorname{Re}(z^4)=1$ and a curve of the $m=2$ family would induce, the two genera being three and two.
--
--   **Formalization Note**: $g(K)$ is `Module.finrank`, which is $0$ for an infinite-dimensional space; the isomorphism is a term of `K ≃ₐ[ℂ] L`.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note): lemma of the formalization, for Remark 5, p. 4, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean: https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/lean/FunctionFieldGenus.lean (C. Perassi)

import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Valuation.ValuationSubring

open CurveSymmetry
set_option autoImplicit false
variable {K L : Type*} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]

theorem CurveSymmetry.genus_congr (e : K ≃ₐ[ℂ] L) : genus K = genus L := by sorry
