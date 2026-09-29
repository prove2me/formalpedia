-- Prove2me | Theorems.Thm_AlgebraicCurve_mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
-- name    : AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/f5ad0d7c-5f88-52b4-b288-02ffd3b9167d
-- title:
--   Reduction of divisors under constant reduction of a smooth curve
-- statement:
--   Let $O$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a prime lying over it in the sense that $p$ is a nonunit of $O$, and assume the residue field $k$ of $O$ is algebraically closed. Let $\pi : X \to \operatorname{Spec} O$ be proper and smooth of relative dimension $1$ with $X$ integral and with integral special fibre $X_k = X \times_{\operatorname{Spec} O} \operatorname{Spec} k$. Assume a descent datum: a discrete valuation domain $O_0$ with an injective ring map $j : O_0 \to O$ such that every natural number prime to $p$ is a unit in $O_0$, a proper, smooth of relative dimension one, geometrically integral $\pi_0 : X_0 \to \operatorname{Spec} O_0$ with a section $\varepsilon_0$ of $\pi_0$, and an isomorphism $e_0 : X \cong X_0 \times_{\operatorname{Spec} O_0} \operatorname{Spec} O$ over $\operatorname{Spec} O$. Let $F/\overline{\mathbb Q}$ be a field which is a curve over $\overline{\mathbb Q}$ (principal divisors exist, all places have residue fields finite over $\overline{\mathbb Q}$, and $\Omega_{F/\overline{\mathbb Q}}$ is free of rank one) and essentially of finite type, with a curve model $\mathfrak M$ (an integral scheme $\mathfrak M.C$, proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$, with an isomorphism $\mathfrak M.\mathrm{ffEquiv} : F \cong \mathfrak M.C$'s function field over the base, a bijection between closed points and places matching stalks with valuation rings, and finite subsets contained in affine opens), together with an isomorphism $e$ from $\mathfrak M.C$ to the generic fibre $X \times_{\operatorname{Spec} O} \operatorname{Spec}\overline{\mathbb Q}$ compatible with the structure morphisms; similarly a field $K/k$ with a curve model $\mathfrak M_k$ and an isomorphism $e_k$ onto the special fibre. Let $\mathcal O_F$ be a valuation subring of $F$ and $\mathrm{res} : \mathcal O_F \to K$ a ring map, subject to: $f \in \mathcal O_F$ exactly when there are an open $U \subseteq X$ containing the image $\xi$ of the generic point of $X_k$, with $U$ meeting the image of $\mathfrak M.C$, and sections $s, t \in \mathcal O_X(U)$ with germ of $t$ at $\xi$ a unit and $f \cdot t = s$ after transporting sections to $F$ through $e$ and $\mathfrak M.\mathrm{ffEquiv}$; $\mathrm{res}$ computed on such sections by restricting them through $e_k$ and $\mathfrak M_k.\mathrm{ffEquiv}$; $\mathrm{res}$ surjective with kernel the maximal ideal of $\mathcal O_F$; and every nonzero $f \in F$ admitting $c \in \overline{\mathbb Q}$ with $c \cdot f \in \mathcal O_F$ and $\mathrm{res}(c \cdot f) \ne 0$. Finally let $\mathrm{red}$ map places of $F/\overline{\mathbb Q}$ to places of $K/k$ so that whenever the $\overline{\mathbb Q}$-point of $X$ attached to a place $P$ through $\mathfrak M$ and $e$ factors as $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec} O \to X$ through a section $Pt$ of $\pi$, the $k$-point attached to $\mathrm{red}\,P$ through $\mathfrak M_k$ and $e_k$ is the restriction of $Pt$ to the closed point. Then for every $f \in \mathcal O_F$ with $\mathrm{res}\,f \ne 0$, every finitely supported divisor $D$ on the places of $F/\overline{\mathbb Q}$ with $D(P) = \operatorname{ord}_P(f)$ for all $P$, and every place $Q$ of $K/k$, the pushforward $\mathrm{red}_* D$ satisfies $(\mathrm{red}_* D)(Q) = \operatorname{ord}_Q(\mathrm{res}\,f)$, where $\operatorname{ord}$ is minus the logarithm of the associated adic valuation.
--
--   This is the divisor-compatibility clause of Deuring's constant reduction of a function field, in the case of a smooth proper relative curve over a place of $\overline{\mathbb Q}$ with unramified prolongation: the pushforward along reduction of places of the divisor of a function that is a unit along the special fibre is the divisor of its reduction. It is used in the construction of a constant reduction attached to such a model, [`AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase`](thm.html#AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase), and relies on the existence of sections with prescribed order one and on the vanishing statement for functions with everywhere trivial order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TopologicalSpace
open AlgebraicCurve

universe v w

theorem AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (he1 : ∀ f : F, f ≠ 0 → ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ 𝒪F, res ⟨c • f, h⟩ ≠ 0)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∀ f : ↥𝒪F, res f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain red D Q = Q.ord (res f) := by sorry
