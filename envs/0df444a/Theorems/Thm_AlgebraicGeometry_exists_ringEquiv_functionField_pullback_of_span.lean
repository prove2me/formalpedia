-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span
-- name    : AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4937a2ee-31f9-5ddc-bc99-d880af1515e8
-- title:
--   Function field of a base change to a valuation ring
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring such that every element of the maximal ideal of $A$ divides, up to some power, any nonzero element of $A$ (i.e. for $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$), and with $A \neq L$ as a subset. Let $A_0$ be a discrete valuation ring that is a domain, $\iota : A_0 \to A$ an injective local ring homomorphism such that every element of $A$ is algebraic over the image subring $\iota(A_0)$. Let $X_0$ be an integral scheme with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$, and $X$ an integral scheme with a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, together with an isomorphism $\mathrm{iso} : X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$, and such that the composite $\mathrm{pr} := \mathrm{iso}$ followed by the first projection carries the generic point of $X$ to the generic point of $X_0$. Let $F$ be a field with an $L$-algebra structure, and $j_0 : K(X_0) \to F$ a ring homomorphism with $j_0(\mathrm{baseToFunctionField}\,\mathrm{toBase}_0\, a) = \iota(a)$ in $F$ for all $a \in A_0$, where `SemistableModel.baseToFunctionField` denotes the canonical map from the base ring to the function field obtained from the global sections of the structure morphism followed by the germ at the generic point. Assume finally that every $f \in F$ is a quotient of two nonzero $L$-linear combinations of elements of $j_0(K(X_0))$: there exist $n$, scalars $c, d : \mathrm{Fin}\,n \to L$ and $g, g' : \mathrm{Fin}\,n \to K(X_0)$ with $\sum_i d_i j_0(g'_i) \neq 0$ and $f \cdot \sum_i d_i j_0(g'_i) = \sum_i c_i j_0(g_i)$. Then there is a ring isomorphism $\varphi : F \xrightarrow{\sim} K(X)$ which sends the image of each $a \in A$ in $F$ to $\mathrm{baseToFunctionField}\,\mathrm{toBase}\,a$, and which satisfies $\varphi \circ j_0 = \mathrm{pr}^{*}$, the latter being the map on stalks at the generic point induced by $\mathrm{pr}$ composed with the specialisation comparison identifying the stalk of $X_0$ at the image point with the stalk at the generic point of $X_0$.
--
--   This is the identification of the function field of a fibre product $X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ with any field $L$-spanned by $K(X_0)$, compatibly with the structure map from $A$ and with pullback along the projection. It is used in the construction of the semistable model of the full-level modular curve over a valuation ring, where $F$ is generated over $L$ by the field of $q$-expansions rational over the residue field of $A_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_span
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    {F : Type} [Field F] [Algebra L F]
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ a : A₀, j₀ (SemistableModel.baseToFunctionField toBase₀ a) = algebraMap L F ((ι a : ↥A) : L))
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → X₀.functionField) (d : Fin n → L)
      (g' : Fin n → X₀.functionField),
      (∑ i, d i • j₀ (g' i)) ≠ 0 ∧ f * (∑ i, d i • j₀ (g' i)) = ∑ i, c i • j₀ (g i)) :
    ∃ φ : F ≃+* X.functionField,
      (∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a) ∧
      (∀ g : X₀.functionField,
        φ (j₀ g) =
          ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
            ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g)) := by sorry
