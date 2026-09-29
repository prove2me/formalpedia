-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData
-- name    : AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3ff0cbc0-e628-5f5f-b4b2-7048666ebc97
-- title:
--   Relative Jacobian from finite-map chart data over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), let $c\colon C\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Assume that for every $m_0\in\mathbb N$ there is a datum `SmoothProperCurve.FiniteMapData c ε` with invariant $m\ge m_0$ satisfying `LevelSetsGenericallyEtale`: affine opens $U,V$ with $U\cup V=C$, $U$ the complement of the image of $\varepsilon$, $U\cap V$ equal to the basic opens of sections $f\in\Gamma(C,U)$ and $g\in\Gamma(C,V)$ whose restrictions multiply to $1$, with $\Gamma(C,U)$ finite over $R[f]$ and $\Gamma(C,V)$ finite over $R[g]$, such that for every local $R$-algebra $S$ and every $s\in S$ the level quotient $S\otimes_R\Gamma(C,U)/(1\otimes f-s\otimes 1)$ is finite free of rank $m$ over $S$, and such that for some $D\in R[t]$ with a unit coefficient this level quotient is étale over $S$ whenever $D(s)$ is a unit (for local $R$-algebras with local structure map). Then there exist a scheme $J$, a morphism $f\colon J\to\operatorname{Spec}R$, a relative group law $L$ on $f$ (a functorial group structure on $T$-points over $\operatorname{Spec}R$, compatible with base change), and a morphism $aj\colon C\to J$ over $\operatorname{Spec}R$, such that: $f$ is smooth and proper with connected fibres $f^{-1}(s)$ and admits a relative group law; $L$ is commutative on $T$-points for every $T\to\operatorname{Spec}R$; $\varepsilon$ followed by $aj$ is the unit section $L.\mathrm{one}$; and for every algebraically closed field $K$, every ring homomorphism $i\colon R\to K$, every field $F$ over $K$ satisfying `IsCurveOver K F` (principal divisors, residue fields of places finite over $K$, and $\Omega_{F/K}$ free of rank $1$ over $F$), every curve model $M$ of $F/K$ and every isomorphism $e\colon M.C\to C\times_{\operatorname{Spec}R}\operatorname{Spec}K$ whose composite with the second projection is $M.\mathrm{toBase}$, there is a bijection $pts$ from $\mathrm{Pic}^0(K,F)$ (degree-zero divisors modulo principal ones) to the set of morphisms $\operatorname{Spec}K\to J$ over $\operatorname{Spec}(i)$ which carries addition to $L.\mathrm{mul}$, and such that for all $K$-points $x,s$ of $M.C$ over $K$ with $s$ transported by $e$ and the first projection equal to $\operatorname{Spec}(i)$ followed by $\varepsilon$, there is a degree-zero divisor $D$ equal to $[\,\text{place of }x\,]-[\,\text{place of }s\,]$ under `pointEquivPlace` whose class satisfies $pts([D])=x$ followed by $e$, the first projection and $aj$.
--
--   This is the construction of the Jacobian of a pointed smooth proper relative curve over a discrete valuation ring, as an abelian scheme with commutative group law together with an Abel–Jacobi embedding killing the marked section and inducing, on geometric fibres, the isomorphism $\mathrm{Pic}^0$ of the fibre curve $\simeq$ the group of points of $J$; the form proved here assumes the existence of finite-map chart data of arbitrarily large degree with generically étale level sets. It feeds the hypothesis-free statement [`AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one`](thm.html#AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one) and, through it, the good-reduction Jacobians of the modular curves attached to $J_H$ and $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve

universe u v

theorem AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) :
    ∃ (J : Scheme.{u}) (f : J ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
      (aj : SchemeHomOver c f),
      AbelianSchemePropertyBundle R f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        L.mul t x y = L.mul t y x) ∧
      ε.1 ≫ aj.1 = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) f,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ D : Divisor.degZero (K := K) (F := F),
              (D : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk D)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by sorry
