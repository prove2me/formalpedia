-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
-- name    : AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c513ad86-5031-5134-98fe-4dc060082023
-- title:
--   Reading rational functions of an R-model in a curve model's function field
-- statement:
--   Let $R$ be a commutative ring, $K$ a field with an $R$-algebra structure whose structure map $R \to K$ is injective, and $L$ a field with a $K$-algebra structure. Let $M$ be a curve model of $L$ over $K$: an integral scheme $M.C$ with a proper, smooth of relative dimension $1$ morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} K$, a ring isomorphism $M.\mathrm{ffEquiv} : L \cong K(M.C)$ sending $\mathrm{algebraMap}\ K\ L\ a$ to the germ at the generic point of the pullback of $a$ along $M.\mathrm{toBase}$, together with a bijection from the closed points of $M.C$ to the places of $L/K$ whose valuation subring is, at each closed point $x$, the image under $M.\mathrm{ffEquiv}^{-1}$ of the stalk $\mathcal{O}_{M.C,x}$ inside $K(M.C)$, and the property that every finite subset of $M.C$ lies in an affine open. Let $X$ be an integral scheme with a morphism $c : X \to \operatorname{Spec} R$, and let $e_0 : M.C \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ be an isomorphism with $e_0$ followed by the second projection equal to $M.\mathrm{toBase}$. Write $f$ for $e_0$ followed by the first projection. Then there is a ring homomorphism $\Theta : K(X) \to L$ such that: (1) for every $P \in X$ with $f(\xi_{M.C}) \rightsquigarrow P$ and every $z \in \mathcal{O}_{X,P}$, applying $M.\mathrm{ffEquiv}^{-1}$ to the image of $z$ under specialisation to $f(\xi_{M.C})$ followed by the stalk map of $f$ at $\xi_{M.C}$ gives $\Theta$ of the image of $z$ in $K(X)$; (2) for every $x \in M.C$ and every $w \in \mathcal{O}_{X,f(x)}$, the image of the stalk map of $f$ at $x$ applied to $w$, taken into $K(M.C)$ and transported by $M.\mathrm{ffEquiv}^{-1}$, equals $\Theta$ of the image of $w$ in $K(X)$; (3) for every $P \in X$ and $r \in R$, $\Theta$ of the class in $K(X)$ of the germ at $P$ of the global section $c^{*}(r)$ equals the image of $r$ in $L$ under $R \to K \to L$; and (4) if the stalk map of $f$ at $\xi_{M.C}$ is an isomorphism, then $\Theta$ is bijective.
--
--   This is the comparison of function fields attached to an integral scheme over $R$ and to a smooth proper curve model of $L/K$ identified with its generic fibre: rational functions on $X$ are read as elements of $L$, compatibly with germs at all points of $X$ in the image of $f$ and with constants from $R$. It is used in the analysis of cusp parameters on modular curves, where clauses (1) and (2) transport $q$-expansion identities into $K(X)$, as in [`ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero`](thm.html#ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero) and the two attendant contradiction lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
    {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {L : Type v} [Field L] [Algebra K L] (M : AlgebraicCurve.CurveModel K L)
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of R))
    (e₀ : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M.toBase) :
    ∃ Θ : X.functionField →+* L,
      (∀ (P : X) (hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M.C) ⤳ P) (z : X.presheaf.stalk P),
        M.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)).hom
          ((X.presheaf.stalkSpecializes hgenP).hom z)) = Θ (algebraMap (X.presheaf.stalk P) X.functionField z)) ∧
      (∀ (x : M.C) (w : X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)),
        M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x) M.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x).hom w)) =
          Θ (algebraMap (X.presheaf.stalk ((e₀ ≫ pullback.fst c _).base x)) X.functionField w)) ∧
      (∀ (P : X) (r : R), Θ (algebraMap (X.presheaf.stalk P) X.functionField
          ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap K L (algebraMap R K r)) ∧
      (IsIso (Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M.C)) → Function.Bijective Θ) := by sorry
