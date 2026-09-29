-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ec489b63-a244-5c8c-83c8-caa9274795f9
-- title:
--   Section of (mathcal I_ε^m)^∨ whose zero scheme misses ε
-- statement:
--   Let $R$ be a Noetherian commutative ring such that every invertible $R$-module is free, and let $c : C \to \operatorname{Spec} R$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\varepsilon_1 : \operatorname{Spec} R \to C$ together with the identity $\varepsilon_1 \mathbin{;} c = \mathrm{id}$, and let $\mathcal V$ be a `TwoAffineOpenCover` of $C$: two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $g$ be a natural number subject to the following hypothesis, which pins $g$ down as the genus of all geometric fibres: for every algebraically closed field $k$, every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} R$, every field $L$ that is a $k$-algebra, every `CurveModel k L` $M$ (a scheme $M.C$, integral, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, with $L$ identified with its function field compatibly with $k$, its closed points in bijection with the places of $L/k$ so that stalks correspond to valuation subrings, and every finite set of points contained in an affine open), every isomorphism $e : M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ over the base (i.e. $e$ followed by the second projection equals $M.\mathrm{toBase}$), every divisor $K_c$ on $L/k$ and every natural number $g'$: if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$, where $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$ and $\deg$ is the degree homomorphism, then $g' = g$. Finally let $m$ be a natural number with $2g \le m$ and $1 \le m$. Then there is a morphism $s$ from the unit object of $C.\mathrm{Modules}$ to the dual of the module attached to the $m$-th power of the ideal sheaf $\ker \varepsilon_1$ — i.e. a global section of $(\mathcal I_\varepsilon^m)^\vee$ — such that no point in the set-theoretic image of $\varepsilon_1$ lies in the support of `Scheme.Modules.zeroSchemeIdeal s`, the smallest ideal sheaf datum whose ideal on each affine open contains the span of the coefficients of $s$ there.
--
--   This is the existence, over a Noetherian base with trivial Picard group, of a global section of $\mathcal O(m\varepsilon)$ on a smooth proper geometrically integral curve whose zero scheme is disjoint from the chosen section $\varepsilon$, for $m \ge \max(2g,1)$. It globalises the corresponding statement at a single maximal ideal of $R$ and feeds the construction of finite map data in [`AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_m_eq_of_forall_invertible_free).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra
open MonoidalCategory
open AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint_of_forall_invertible_free
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m) (hm₁ : 1 ≤ m) :
    ∃ s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule,
      ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by sorry
