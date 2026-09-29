-- Prove2me | Theorems.Thm_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
-- name    : AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/54fdff4c-1f6f-534d-a981-88338abcabfe
-- title:
--   Order zero is preserved by reduction at a smooth special point
-- statement:
--   Let $O$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a prime such that $p$ is a non-unit of $O$, and assume the residue field of $O$ is algebraically closed. Let $\pi : X \to \operatorname{Spec} O$ be proper and smooth of relative dimension $1$ with $X$ integral and the special fibre $X_k = X \times_{\operatorname{Spec} O} \operatorname{Spec} k$ integral, where $k$ is the residue field. Assume a descent datum: a discrete valuation ring $O_0$ with an injective ring homomorphism $j : O_0 \to O$ such that every natural number prime to $p$ is a unit in $O_0$, a proper, geometrically integral morphism $\pi_0 : X_0 \to \operatorname{Spec} O_0$ smooth of relative dimension $1$, a section $\varepsilon_0$ of $\pi_0$, and an isomorphism $e_0 : X \xrightarrow{\sim} X_0 \times_{\operatorname{Spec} O_0} \operatorname{Spec} O$ over $\operatorname{Spec} O$. Let $F$ be an essentially finite type extension field of $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ (principal divisors exist, all places have residue fields finite over $\overline{\mathbb Q}$, and $\Omega_{F/\overline{\mathbb Q}}$ is free of rank one), $\mathfrak M$ a curve model of $F/\overline{\mathbb Q}$ together with an isomorphism $e$ of $\mathfrak M.C$ with the generic fibre $X \times_{\operatorname{Spec} O} \operatorname{Spec}\overline{\mathbb Q}$ over $\operatorname{Spec}\overline{\mathbb Q}$, and similarly $K/k$ a field with a curve model $\mathfrak M_k$ and an isomorphism $e_k$ of $\mathfrak M_k.C$ with $X_k$ over $\operatorname{Spec} k$. Let $\mathcal O_F$ be a valuation subring of $F$ and $\mathrm{res} : \mathcal O_F \to K$ a ring homomorphism such that: $f \in \mathcal O_F$ exactly when there are an open $U \subseteq X$ containing the image $\xi$ in $X$ of the generic point of $X_k$, with $U$ meeting the generic fibre, and sections $s, t$ over $U$ with the germ of $t$ at $\xi$ a unit and $f$ times the image of $t$ in $F$ equal to the image of $s$ in $F$ (so $\mathcal O_F$ is the local ring of $X$ at $\xi$ read inside $F$); $\mathrm{res}$ sends the element of $\mathcal O_F$ cut out by a section $s$ over such a $U$ meeting both fibres to the image of $s$ in $K$ via $e_k$; $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O_F$; and every $f \neq 0$ in $F$ admits $c \in \overline{\mathbb Q}$ with $c \cdot f \in \mathcal O_F$ and $\mathrm{res}(c \cdot f) \neq 0$. Finally let $\mathrm{red}$ be a map from places of $F/\overline{\mathbb Q}$ to places of $K/k$ compatible with specialisation of $O$-points: whenever the $\overline{\mathbb Q}$-point of $X$ attached to a place $P$ via $\mathfrak M$.`pointEquivPlace` and $e$ is the generic fibre of a section $Pt$ of $\pi$, the $k$-point attached to $\mathrm{red}\,P$ via $\mathfrak M_k$ and $e_k$ is the special fibre of $Pt$. The conclusion: for every $g \in \mathcal O_F$ with $\mathrm{res}\,g \neq 0$ and every place $Q$ of $K/k$, if $\operatorname{ord}_P(g) = 0$ for all places $P$ of $F/\overline{\mathbb Q}$ with $\mathrm{red}\,P = Q$, then $\operatorname{ord}_Q(\mathrm{res}\,g) = 0$, where $\operatorname{ord}$ denotes minus the logarithm of the associated adic valuation.
--
--   This is the locality statement for reduction on a smooth proper relative curve in divisor form: a function that is a unit at the generic point of the special fibre and has neither zero nor pole at any place of the generic fibre specialising to a given place $Q$ of the special fibre reduces to a function with neither zero nor pole at $Q$. It is used by [`AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem`](thm.html#AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem), which compares the divisor of $g$ pushed forward along $\mathrm{red}$ with the divisor of $\mathrm{res}\,g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve TopologicalSpace

universe v w

theorem AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
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
    ∀ (g : F) (hg : g ∈ 𝒪F), res ⟨g, hg⟩ ≠ 0 →
      ∀ Q : Place (IsLocalRing.ResidueField ↥O) K,
        (∀ P : Place (AlgebraicClosure ℚ) F, red P = Q → P.ord g = 0) → Q.ord (res ⟨g, hg⟩) = 0 := by sorry
