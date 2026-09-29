-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
-- name    : AlgebraicCurve.exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/fa67c1e4-d12e-529c-bc14-61f27e7874ff
-- title:
--   Local equation of a horizontal section of a relative curve
-- statement:
--   Let $O$ be a valuation subring of $\overline{\mathbb Q}$ such that a prime $p$ is a nonunit of $O$ (the content of `LiesOverPrime`) and whose residue field is algebraically closed. Let $\pi : X \to \operatorname{Spec} O$ be proper and smooth of relative dimension one with $X$ integral and the fibre product of $\pi$ along $\operatorname{Spec}$ of the residue map $O \to k$ integral. Let $F$ be a field over $\overline{\mathbb Q}$, essentially of finite type, satisfying `IsCurveOver`: every nonzero $f$ has a degree-zero divisor recording $\operatorname{ord}_v f$ at all places, each place has residue field finite over $\overline{\mathbb Q}$, and $\Omega_{F/\overline{\mathbb Q}}$ is free of rank one. Let $\mathfrak M$ be a `CurveModel` of $F$ over $\overline{\mathbb Q}$ (an integral scheme $C$, proper and smooth of relative dimension one over $\operatorname{Spec}\overline{\mathbb Q}$, with $F \cong C$'s function field, a bijection from closed points to places matching stalks with valuation subrings, and finite sets of points inside affine opens), together with an isomorphism $e$ from $\mathfrak M.C$ to the generic fibre $X \times_{\operatorname{Spec} O} \operatorname{Spec}\overline{\mathbb Q}$ commuting with the structure maps; likewise a field $K$ over $k$, a `CurveModel` $\mathfrak M_k$ of $K$ over $k$, and an isomorphism $e_k$ onto the special fibre over $\operatorname{Spec} k$. Let $\mathcal O_F \subseteq F$ be a valuation subring and $\operatorname{res} : \mathcal O_F \to K$ a ring homomorphism, pinned by: $f \in \mathcal O_F$ exactly when on some open $U \subseteq X$ containing the image $\xi$ of the generic point of the special fibre, with $U$ meeting the generic fibre, there are $s, t \in \Gamma(X, U)$ with germ of $t$ at $\xi$ a unit and $f$ times the element of $F$ determined by $t$ equal to that determined by $s$ (sections being transported to $F$ through $e$ and the function field of $\mathfrak M.C$); $\operatorname{res}$ sends the element of $F$ determined by any such $s$ to the element of $K$ determined by $s$ through $e_k$ and $\mathfrak M_k$; $\operatorname{res}$ is surjective with kernel the maximal ideal of $\mathcal O_F$. Finally let $\operatorname{red}$ map places of $F/\overline{\mathbb Q}$ to places of $K/k$, compatibly with $O$-sections of $\pi$: whenever the $\overline{\mathbb Q}$-point of $\mathfrak M.C$ corresponding to $P$ arises from a section $Pt$ of $\pi$ by base change along $O \hookrightarrow \overline{\mathbb Q}$, the $k$-point corresponding to $\operatorname{red} P$ arises from $Pt$ by base change along $O \to k$. The conclusion: for every place $P$ of $F/\overline{\mathbb Q}$ there is $u \in F$ with $u$ and $u^{-1}$ in $\mathcal O_F$, $\operatorname{ord}_P u = 1$, $\operatorname{ord}_{P'} u = 0$ for every place $P' \neq P$ with $\operatorname{red} P' = \operatorname{red} P$, and $\operatorname{ord}_{\operatorname{red} P}(\operatorname{res} u) = 1$.
--
--   This is the existence of a local equation, along the horizontal section through $P$ given by the valuative criterion of properness, of a function that is a unit of the local ring of $X$ at the generic point of the special fibre, has a simple zero at $P$ and no other zero or pole in the residue disc of $P$, and whose reduction is a uniformiser at $\operatorname{red} P$; it belongs to Deuring-style reduction theory for function fields. It is used by [`AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem`](thm.html#AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem) to compare divisors on the generic and the special fibre under reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one.lean

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

theorem AlgebraicCurve.exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

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

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∀ P : Place (AlgebraicClosure ℚ) F, ∃ (u : F) (hu : u ∈ 𝒪F), u⁻¹ ∈ 𝒪F ∧ P.ord u = 1 ∧
      (∀ P' : Place (AlgebraicClosure ℚ) F, red P' = red P → P' ≠ P → P'.ord u = 0) ∧
      (red P).ord (res ⟨u, hu⟩) = 1 := by sorry
