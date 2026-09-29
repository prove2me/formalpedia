-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_local_lifts
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_local_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c35fdc3a-b9d8-5e5a-beea-3310d74ddbb2
-- title:
--   Chart rings of the special fibre via local lifts
-- statement:
--   Fix a commutative local ring $T'$, a commutative ring $T$ and a ring map $\pi\colon T'\to T$; a scheme $A_0$ with a separated morphism $f_0\colon A_0\to\operatorname{Spec} T$; a ring map $\rho\colon T\to$ `ResidueField T'` with $\rho\circ\pi$ the residue map of $T'$; and an ordered affine cover $\mathcal U$ of $A_0$, that is, a finite linearly ordered index type $\iota$ together with affine opens $U_a\subseteq A_0$ whose supremum is $\top$. Assume given, for each $a$, a scheme $Y_a$ with $q_a\colon Y_a\to\operatorname{Spec} T'$ and $g_a\colon U_a\to Y_a$ such that the square formed by $g_a$, the inclusion $U_a\hookrightarrow A_0$ followed by $f_0$, $q_a$ and $\operatorname{Spec}\pi$ is cartesian; a scheme $A_k$ with a separated $f_k\colon A_k\to\operatorname{Spec}(\mathrm{ResidueField}\, T')$ and an affine morphism $i_0\colon A_k\to A_0$ making the square of $i_0$, $f_k$, $f_0$, $\operatorname{Spec}\rho$ cartesian; and maps $O_a$ from the opens of $A_0$ to the opens of $Y_a$ satisfying $g_a^{-1}(O_a(W))=$ the preimage of $W$ in $U_a$, monotonicity, $O_a(U_a)=\top$, $O_a(W)\cap O_a(W')\le O_a(W\cap W')$, and affineness of $O_a(W)$ whenever $W$ is affine with $W\le U_a$. The conclusion asserts the existence, for every $n$ and every $s\in\mathcal U.\mathrm{Idx}\,n$ (a strictly monotone $s\colon \mathrm{Fin}(n+1)\to\iota$), writing $a=s(0)$ and $U_s=\bigwedge_j U_{s(j)}$, of a ring isomorphism $$\sigma_s\colon \mathrm{ResidueField}\, T'\otimes_{T'}\Gamma(Y_a,O_a(U_s))\;\xrightarrow{\ \sim\ }\;\Gamma\bigl(A_k,\textstyle\bigwedge_j i_0^{-1}U_{s(j)}\bigr),$$ the $T'$-algebra structure on the left being the one induced by $q_a$, subject to two conditions: first, the canonical isomorphism of the affine open $\bigwedge_j i_0^{-1}U_{s(j)}$ with the spectrum of its sections, followed by $\operatorname{Spec}$ of $\sigma_s$, then $\operatorname{Spec}$ of $x\mapsto 1\otimes x$, then the structure morphism $\operatorname{Spec}\Gamma(Y_a,O_a(U_s))\to Y_a$ of the affine open $O_a(U_s)$, equals the composite of the inclusion $\bigwedge_j i_0^{-1}U_{s(j)}\le i_0^{-1}U_s$, the restriction of $i_0$ over $U_s$, the inclusion $U_s\le U_a$ and $g_a$; and second, $\sigma_s(x\otimes 1)$ is the image of $x$ under the structure map of $\Gamma(A_k,\bigwedge_j i_0^{-1}U_{s(j)})$ as an algebra over `ResidueField T'` coming from $f_k$, for all $x$.
--
--   This identifies the Čech chart rings of the special fibre $A_k$ with the reductions modulo the maximal ideal of the chart rings of the local lifts $Y_a$, the isomorphisms being pinned by the requirement that their spectra realise the geometric maps from the chart intersections of $A_k$ into the lifts; the pinning is necessarily phrased scheme-theoretically, since no global morphism $A_k\to Y_a$ is available. It is used in the construction of the obstruction $2$-cocycle attached to a small extension from local lifts, by [`AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts`](thm.html#AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_local_lifts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_local_lifts
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = IsLocalRing.residue T')
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T'))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W)) :
    ∃ (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s)),
      (∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0)) ∧
      (∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x) := by sorry
