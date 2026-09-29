-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime
-- name    : AlgebraicCurve.exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/470e2215-fafd-58e5-8e72-0a939c625a6c
-- title:
--   Constant reduction at the generic point of the special fibre
-- statement:
--   Let $\mathcal O$ be a valuation subring of $\overline{\mathbb Q}$ and $p$ a prime such that $p$ is a non-unit of $\mathcal O$ (the meaning of `LiesOverPrime`), with $\mathcal O$'s residue field algebraically closed. Let $\pi : X \to \operatorname{Spec}\mathcal O$ be proper and smooth of relative dimension one, with $X$ integral and with integral special fibre $X \times_{\mathcal O} \mathcal O/\mathfrak m$. Assume given a discrete valuation domain $\mathcal O_0$, an injective ring map $j : \mathcal O_0 \to \mathcal O$ such that every natural number prime to $p$ is a unit of $\mathcal O_0$ and such that $j$ reflects units, a proper, smooth of relative dimension one, geometrically integral $\pi_0 : X_0 \to \operatorname{Spec}\mathcal O_0$ together with a section of $\pi_0$, and an isomorphism $e_0 : X \xrightarrow{\sim} X_0 \times_{\mathcal O_0} \mathcal O$ over $\operatorname{Spec}\mathcal O$. Let $F/\overline{\mathbb Q}$ be a field that is a curve over $\overline{\mathbb Q}$ in the project's sense (principal divisors exist, all places have residue field finite over $\overline{\mathbb Q}$, and $\Omega_{F/\overline{\mathbb Q}}$ is free of rank one) and of essentially finite type, and let $\mathfrak M$ be a curve model of $F/\overline{\mathbb Q}$, i.e. an integral scheme $\mathfrak M.C$, proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$, with an isomorphism $\mathfrak M.\mathrm{ffEquiv} : F \cong \overline{\mathbb Q}(\mathfrak M.C)$ compatible with constants, a bijection from closed points to places of $F/\overline{\mathbb Q}$ matching stalks with valuation rings, and every finite set of points contained in an affine open; suppose $\mathfrak M.C \cong X \times_{\mathcal O} \overline{\mathbb Q}$ over $\operatorname{Spec}\overline{\mathbb Q}$. Symmetrically, let $K$ be a field over the residue field $k$ of $\mathcal O$, and $\mathfrak M_k$ a curve model of $K/k$ with $\mathfrak M_k.C \cong X \times_{\mathcal O} k$ over $\operatorname{Spec} k$. Then there exist a valuation subring $\mathcal O_F \subseteq F$ and a ring homomorphism $\mathrm{res} : \mathcal O_F \to K$ with the following properties. Writing $\xi$ for the image in $X$ of the generic point of the special fibre, and writing $u \mapsto \mathfrak M.\mathrm{ffEquiv}^{-1}$ of the germ at the generic point of the pullback of $u$ along $\mathfrak M.C \to X$ for the map sending a section of $X$ to an element of $F$ (and similarly into $K$ via $\mathfrak M_k.C \to X$): an element $f \in F$ lies in $\mathcal O_F$ exactly when there are an open $U \subseteq X$ with $\xi \in U$ and with nonempty preimage in $\mathfrak M.C$, and sections $s, t \in \mathcal O_X(U)$ such that the germ of $t$ at $\xi$ is a unit and $f$ times the image of $t$ in $F$ equals the image of $s$ in $F$; for every open $U$ with nonempty preimages in both $\mathfrak M.C$ and $\mathfrak M_k.C$ and every $s \in \mathcal O_X(U)$ whose image in $F$ lies in $\mathcal O_F$, $\mathrm{res}$ of that image is the image of $s$ in $K$; $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O_F$; for $c \in \overline{\mathbb Q}$ one has $c \in \mathcal O_F$ iff $c \in \mathcal O$; every nonzero $f \in F$ has a scalar $c \in \overline{\mathbb Q}$ with $c f \in \mathcal O_F$ and $\mathrm{res}(cf) \neq 0$; and for $a \in \mathcal O$ the constant $a$ lies in $\mathcal O_F$ with $\mathrm{res}(a)$ the image of the residue of $a$ in $K$.
--
--   This is the existence part of Deuring's constant reduction for a function field with good reduction: the local ring of $X$ at the generic point of the special fibre is realised as a valuation ring of $F$ whose residue map recovers the function field of the special fibre and extends reduction on constants. It supplies the integers, the residue map, the surjectivity and kernel statement, and the compatibility with constants used by [`AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase`](thm.html#AlgebraicCurve.exists_constantReduction_of_smoothOfRelativeDimension_one_liesOverPrime_fixedBase).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve TopologicalSpace

universe v w

theorem AlgebraicCurve.exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))

    (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
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
    :
    ∃ (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K),

      (∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s))) ∧

      (∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s))) ∧

      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F ∧

      (∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) F c ∈ 𝒪F ↔ c ∈ O) ∧

      (∀ f : F, f ≠ 0 → ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ 𝒪F, res ⟨c • f, h⟩ ≠ 0) ∧

      (∀ a : ↥O, ∃ h : algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ 𝒪F,
        res ⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), h⟩ =
          algebraMap (IsLocalRing.ResidueField ↥O) K (IsLocalRing.residue ↥O a)) := by sorry
