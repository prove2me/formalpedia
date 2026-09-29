-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d062e65a-3de8-53f1-bccf-7efbefc5662e
-- title:
--   Arithmetic-progression twists by invertible ideal sheaves are trivial
-- statement:
--   Let $Y$ be a scheme and let $I_0,\dots,I_e$ be quasi-coherent ideal sheaf data on $Y$, each satisfying the predicate `IsInvertible`: for every point $x$ of $Y$ there are an affine open $U$ and $f \in \Gamma(Y,U)$ with $x$ in the basic open set of $f$, together with a non-zerodivisor $g$ in the sections over the affine basic open set of $f$ such that the ideal cut out there by $I_k$ is $(g)$. Let $\varpi, w$ be endomorphisms of the unit object $\mathbf 1$ of the monoidal category $Y$-modules, and assume $\prod_k I_k$ equals the zero-scheme ideal of $\varpi$ and $\prod_k I_k^{\,k}$ equals the zero-scheme ideal of $w$, where the zero-scheme ideal of a section $s$ is the infimum of all ideal sheaf data whose ideal on each affine open contains the span of the coefficients of $s$ there. Let $v^+, v^- : \{0,\dots,e\} \to \mathbb N$ and $a_0, d \in \mathbb Z$ satisfy $v^+_k - v^-_k = a_0 + k\,d$ for all $k$. Then there exists an isomorphism $$\bigl(\textstyle\prod_k I_k^{\,v^+_k}\bigr)^{\vee\text{-module}} \otimes \bigl(\textstyle\prod_k I_k^{\,v^-_k}\bigr)^{\text{module}} \cong \mathbf 1,$$ where for an ideal sheaf $J$ the module $J^{\text{module}}$ is the kernel of the map from $\mathcal O_Y$ to the pushforward of $\mathcal O$ along the closed immersion of the subscheme defined by $J$, and $J^{\vee\text{-module}}$ is its internal dual $\underline{\mathrm{Hom}}(J^{\text{module}},\mathbf 1)$; only nonemptiness of the type of such isomorphisms is asserted.
--
--   In classical language: if the effective Cartier divisors $C_k$ attached to the $I_k$ satisfy the two relations $\sum_k C_k = \operatorname{div}\varpi$ and $\sum_k k\,C_k = \operatorname{div} w$, then any twist $\mathcal O_Y(\sum_k a_k C_k)$ whose coefficients $a_k = v^+_k - v^-_k$ form an arithmetic progression in $k$ is trivial, since it equals $a_0 \operatorname{div}\varpi + d\operatorname{div} w$. It is used in the resolution machinery, via [`MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero`](thm.html#MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero), to trivialise vertical twists of degree zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
    {Y : Scheme.{u}} {e : ℕ} (I : Fin (e + 1) → Y.IdealSheafData) (hI : ∀ k, (I k).IsInvertible)
    (ϖ w : 𝟙_ Y.Modules ⟶ 𝟙_ Y.Modules)
    (hϖ : ∏ k, I k = Scheme.Modules.zeroSchemeIdeal ϖ)
    (hw : ∏ k, I k ^ (k : ℕ) = Scheme.Modules.zeroSchemeIdeal w)
    (vp vn : Fin (e + 1) → ℕ) (a₀ d : ℤ)
    (hAP : ∀ k : Fin (e + 1), (vp k : ℤ) - (vn k : ℤ) = a₀ + ((k : ℕ) : ℤ) * d) :
    Nonempty ((∏ k, I k ^ vp k).invModule ⊗ (∏ k, I k ^ vn k).module ≅ 𝟙_ Y.Modules) := by sorry
