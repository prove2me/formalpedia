-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_subring_ringEquiv_stalk_of_iso_pullback
-- name    : AlgebraicCurve.exists_subring_ringEquiv_stalk_of_iso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/eecbefed-7e58-5c4d-afc5-80ef8b24f576
-- title:
--   Stalk of a model descends to a local subring of F
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure. Let $X$ be an integral scheme with a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, and let $\varphi : F \xrightarrow{\sim} K(X)$ be a ring isomorphism onto the function field of $X$ such that for every $a \in A$ the element $\varphi(a \cdot 1_F)$ is the germ at the generic point of $X$ of the global section obtained from $a$ by $\mathrm{toBase}$ (the map `SemistableModel.baseToFunctionField`). Let $A_0$ be a discrete valuation ring, $\iota_0 : A_0 \to A$ an injective local ring homomorphism, and $X_0$ an integral scheme with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ that is locally of finite presentation. Assume given an isomorphism $\mathrm{iso}$ of $X$ with the pullback of $\mathrm{toBase}_0$ along $\operatorname{Spec}(\iota_0)$ whose composite with the second projection is $\mathrm{toBase}$, and let $x \in X$. Write $\mathcal N \subseteq F$ for `SemistableModel.localRing`, the image in $F$ under $\varphi^{-1}$ of the image of $\mathcal O_{X,x} \to K(X)$, and let $\mathrm{pr} : X \to X_0$ be $\mathrm{iso}$ followed by the first projection. Then there are a subring $\mathcal N_0 \subseteq F$ and a ring isomorphism $\theta : \mathcal O_{X_0,\mathrm{pr}(x)} \xrightarrow{\sim} \mathcal N_0$ such that: $\theta(g) = \varphi^{-1}$ of the image of $g$ under the stalk map of $\mathrm{pr}$ at $x$ followed by $\mathcal O_{X,x} \to K(X)$, for all $g$; $f \in \mathcal N_0$ if and only if $\varphi(f)$ is the image in $K(X)$ of some $g \in \mathcal O_{X_0,\mathrm{pr}(x)}$; $\mathcal N_0 \le \mathcal N$; $\mathcal N_0$ is local and Noetherian; for every $a \in A_0$ the image of $\iota_0(a) \in A \subseteq L$ in $F$ lies in $\mathcal N_0$, and $\theta$ sends the germ at $\mathrm{pr}(x)$ of the global section of $X_0$ coming from $a$ to that element.
--
--   This is the descent step which identifies the local ring at a point of a base-changed model with a concrete local Noetherian subring of $F$ containing the constants $\iota_0(A_0)$, together with the membership criterion through which later steps refer to it. It is used in the construction of semistable models over a finite level, where the finitely presented model $X_0$ over a discrete valuation ring $A_0 \subseteq A$ replaces $X$ over the valuation ring $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_subring_ringEquiv_stalk_of_iso_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_subring_ringEquiv_stalk_of_iso_pullback
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)
    (x : X) :
    let 𝒩 : Subring F := SemistableModel.localRing X φ x
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))
    ∃ (𝒩₀ : Subring F) (θ : X₀.presheaf.stalk (pr.base x) ≃+* ↥𝒩₀),
      (∀ g : X₀.presheaf.stalk (pr.base x),
        ((θ g : ↥𝒩₀) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField ((pr.stalkMap x).hom g))) ∧
      (∀ f : F, f ∈ 𝒩₀ ↔ ∃ g : X₀.presheaf.stalk (pr.base x),
        φ f = algebraMap (X.presheaf.stalk x) X.functionField ((pr.stalkMap x).hom g)) ∧
      𝒩₀ ≤ 𝒩 ∧ IsLocalRing ↥𝒩₀ ∧ IsNoetherianRing ↥𝒩₀ ∧
      (∀ a : A₀, algebraMap L F ((ι₀ a : ↥A) : L) ∈ 𝒩₀) ∧
      (∀ a : A₀, ((θ ((X₀.presheaf.germ ⊤ (pr.base x) trivial).hom
          (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) : ↥𝒩₀) : F) =
        algebraMap L F ((ι₀ a : ↥A) : L)) := by sorry
