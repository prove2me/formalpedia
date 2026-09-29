-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/46f78150-6247-5801-b26e-0248f8845722
-- title:
--   Alternating behaviour of the defect tangent coordinates
-- statement:
--   Let $T'$ be a local artinian ring and $T$ a ring, let $\pi\colon T'\to T$ satisfy $(\ker\pi)\cdot\mathfrak m_{T'}=0$ and $\ker\pi\subseteq\mathfrak m_{T'}$, and let $\rho\colon T\to k:=\mathrm{ResidueField}\,T'$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $V$ be a finite-dimensional $k$-vector space, also a $T'$-module compatibly with the $k$-structure, and $\iota\colon V\to T'$ an injective $T'$-linear map with image exactly $\ker\pi$. Let $f_0\colon A_0\to\operatorname{Spec}T$ be separated, $\mathcal U$ an ordered affine cover of $A_0$ (finite linearly ordered index set, affine opens $U_a$ with $\bigsqcup_a U_a=\top$), and for each $a$ a smooth $Y_a\to\operatorname{Spec}T'$ together with $g_a\colon U_a\to Y_a$ making $U_a$ the base change of $Y_a$ along $\operatorname{Spec}\pi$. Let $f_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ (functorial multiplication, unit, inverse over all test bases, with the group axioms and naturality), let $i_0\colon A_k\to A_0$ exhibit $A_k$ as the base change of $A_0$ along $\operatorname{Spec}\rho$, and let $U_e\subseteq A_k$ be an affine open carrying a section $e_1$ of the unit of $L_k$. Let $O_a$ assign to each open $W\subseteq A_0$ an open $O_a(W)\subseteq Y_a$ with $g_a^{-1}O_a(W)=U_a\cap W$, monotonically, and affine for $W$ affine inside $U_a$; let transitions $\Phi_{a,b,W}\colon O_a(W)\xrightarrow{\sim}O_b(W)$ be given for every ordered pair $a,b$ and every $W\subseteq U_a\cap U_b$, commuting with the structure maps to $\operatorname{Spec}T'$, carrying the reduction of $g_a$ to that of $g_b$, compatible with restriction to smaller opens, equal to the identity for $a=b$, and inverse to $\Phi_{b,a,W}$. Finally let $f\colon\{0,1,2\}\to\mathcal U.\iota$ be an arbitrary index triple, $W\subseteq\bigcap_j U_{f(j)}$, $C$ a flat $T'$-algebra, $\ell\colon\operatorname{Spec}C\to O_{f(0)}(W)$ a morphism over $T'$, and let $D$ assign to each $a\in\Gamma(A_k,U_e)$ a $k$-linear map $V^\vee\to k\otimes_{T'}C$ which is a system of tangent coordinates, in the chart $U_e$ and relative to the comparison datum $(i_0^{-1}U_{f(2)},\;(i_0|_{U_{f(2)}})\circ g_{f(2)})$, of the pair of $C$-points of $Y_{f(2)}$ given by $\ell$ followed by $\Phi_{f(0),f(2),W}$ and by $\ell$ followed by $\Phi_{f(0),f(1),W}$ then $\Phi_{f(1),f(2),W}$: that is, there are a point of $i_0^{-1}U_{f(2)}$ over the thickening $(k\otimes_{T'}C)\otimes_k(k\oplus V)$ lying over the canonical base, witnessing that the two points differ by that tangent datum, and its $L_k$-translate into $U_e$, from whose chart ring homomorphism $D$ is read off. The conclusion has two parts. First, if $f$ is not injective then $D(a)=0$ for all $a\in\Gamma(A_k,U_e)$. Second, if $f$ is injective then for every strictly increasing triple $r$ of indices with $r(j)=f(\mathrm{sort}(f)(j))$ for all $j$, every $W\subseteq\bigcap_j U_{r(j)}$, every system $cs$ of tangent coordinates of the corresponding defect pair on the affine open $O_{r(0)}(\bigcap_j U_{r(j)})$ (its spectrum mapped by the transitions into $Y_{r(2)}$, same comparison open $i_0^{-1}U_{r(2)}$ and chart $U_e$), and every $T'$-algebra map $\theta\colon\Gamma(Y_{r(0)},O_{r(0)}(\bigcap_j U_{r(j)}))\to C$ whose spectrum composed with the canonical isomorphism of that affine open realises $\ell$ followed by $\Phi_{f(0),r(0),W}$ and the restriction $O_{r(0)}(W)\to O_{r(0)}(\bigcap_j U_{r(j)})$, one has $D(a)(\xi)=\mathrm{sign}(\mathrm{sort}(f))\cdot(\mathrm{id}_k\otimes\theta)(cs(a)(\xi))$ for all $a\in\Gamma(A_k,U_e)$ and $\xi\in V^\vee$.
--
--   This is the chart-level statement that the obstruction $2$-cochain attached to a family of smooth local lifts is alternating: its value on an arbitrary triple of cover indices vanishes when two indices coincide, and otherwise equals the value on the sorted triple, pulled back along the test algebra and multiplied by the sign of the sorting permutation. It is used in the comparison of the obstruction cocycle with the coboundary of a one-cochain after pullback along a non-monotone refinement of indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)

    (f : Fin 3 → 𝒰.ι) (W : A₀.Opens) (hW : ∀ j, W ≤ 𝒰.U (f j))
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    (ℓ : Spec (CommRingCat.of C) ⟶ ↑(O (f 0) W))
    (hℓ : ℓ ≫ (O (f 0) W).ι ≫ q (f 0) = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (D : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C)))
    (hD : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C
      (ℓ ≫ (Φ (f 0) (f 2) W (hW 0) (hW 2)).hom ≫ (O (f 2) W).ι)
      (ℓ ≫ (Φ (f 0) (f 1) W (hW 0) (hW 1)).hom ≫ (Φ (f 1) (f 2) W (hW 1) (hW 2)).hom ≫ (O (f 2) W).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (f 2)) ((i₀ ∣_ 𝒰.U (f 2)) ≫ g (f 2)) Ue D) :
    (¬ Function.Injective f → ∀ a : Γ(Ak, Ue), D a = 0) ∧
    (∀ (hinj : Function.Injective f) (r : 𝒰.Idx 2) (hr : ∀ j, r.1 j = f ((Tuple.sort f) j))
      (hWr : W ≤ 𝒰.inter r),
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ∀ (cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))
        (hcs : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (Φ (r.1 0) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (Φ (r.1 0) (r.1 1) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 1)).hom ≫
              (Φ (r.1 1) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 1) (𝒰.inter_le r 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs)
        (θ : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) →ₐ[T'] C)
        (hθ : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
            (hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv =
          ℓ ≫ (Φ (f 0) (r.1 0) W (hW 0) ((hWr.trans (𝒰.inter_le r 0)))).hom ≫
            (Y (r.1 0)).homOfLE (hOm (r.1 0) hWr)),
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        D a ξ = ((Equiv.Perm.sign (Tuple.sort f) : ℤˣ) : ℤ) •
          (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) θ) (cs a ξ)) := by sorry
