-- Prove2me | Theorems.Thm_CurveSymmetry_mem_regularAt_iff_of_generator
-- name    : CurveSymmetry.mem_regularAt_iff_of_generator
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-07T12:44:57.244908+00:00
-- url     : https://prove2.me/theorems/ec53908d-d69c-43d8-9168-3af294e27f54
-- title:
--   Regularity at a valuation ring whose differentials are all multiples of a single $du$
-- statement:
--   Let $K$ be a field containing $\mathbb C$ (a field with a $\mathbb C$-algebra structure), $\Omega_{K/\mathbb C}$ its module of Kähler differentials and $d\colon K\to\Omega_{K/\mathbb C}$ the universal derivation. A *valuation ring* of $K$ is a subring $\mathcal O\subseteq K$ such that $\xi\in\mathcal O$ or $\xi^{-1}\in\mathcal O$ for every nonzero $\xi\in K$. A differential is *regular at* $\mathcal O$ if it is a $\mathbb C$-linear combination of differentials $a\,db$ with $a,b\in\mathcal O$; these form a subspace $\operatorname{Reg}(\mathcal O)\subseteq\Omega_{K/\mathbb C}$.
--
--   Let $\mathcal O$ be a valuation ring of $K$ and $u\in\mathcal O$, and assume:
--
--   1. $\mathcal O$ contains $\mathbb C$;
--   2. for every $b\in\mathcal O$ there is $g\in\mathcal O$ with $db=g\,du$.
--
--   Then, for every $\omega\in\Omega_{K/\mathbb C}$,
--
--   $$\omega\in\operatorname{Reg}(\mathcal O)\iff\omega=f\,du\ \text{ for some }f\in\mathcal O.$$
--
--   This links the intrinsic notion of regularity, used to define the genus of a function field without choosing a model, with the uniformizer criterion of explicit computations. It is applied at the points of the double cover $w^2=-t(t^m+1)(\alpha t^m+\bar\alpha)$ attached to the family and at the points of the Kummer covers $y^n=f(x)$, in the comparison of genera behind Remark 5: two for the $m=2$ family, three for $\operatorname{Re}(z^4)=1$.
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
variable {K : Type*} [Field K] [Algebra ℂ K]

theorem CurveSymmetry.mem_regularAt_iff_of_generator {O : ValuationSubring K} {u : K} (hu : u ∈ O)
    (hconst : ∀ z : ℂ, algebraMap ℂ K z ∈ O)
    (hgen : ∀ b ∈ O, ∃ g ∈ O,
      KaehlerDifferential.D ℂ K b = g • KaehlerDifferential.D ℂ K u)
    (ω : Ω[K⁄ℂ]) :
    ω ∈ regularAt O ↔ ∃ f ∈ O, ω = f • KaehlerDifferential.D ℂ K u := by sorry
