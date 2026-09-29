-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_smooth_isPullback_of_local_lifts_of_overlap_isos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/5ba3d11a-ed5b-5570-8202-6e4de5975aaf
-- title:
--   Gluing smooth local lifts along overlap isomorphisms
-- statement:
--   Let $\pi \colon T' \to T$ be a homomorphism of commutative rings, let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes, and let $\mathcal U$ be an ordered affine cover of $A_0$: a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq A_0$, each affine, whose supremum is $\top$. Assume given for each $a$ a scheme $Y_a$ with a smooth morphism $q_a \colon Y_a \to \operatorname{Spec} T'$ and a morphism $g_a \colon U_a \to Y_a$ making the square formed by $g_a$, the composite of the inclusion $U_a \hookrightarrow A_0$ with $f_0$, $q_a$ and $\operatorname{Spec}\pi$ cartesian; a map $O_a$ from opens of $A_0$ to opens of $Y_a$ with $g_a^{-1}(O_a(W)) = U_a \cap W$ (as opens of $U_a$), monotone, with $O_a(U_a) = \top$ and $O_a(W) \cap O_a(W') \le O_a(W \cap W')$; for each $a < b$ an isomorphism $\varphi_{ab} \colon O_a(U_a \cap U_b) \cong O_b(U_a \cap U_b)$ commuting with the structure morphisms to $\operatorname{Spec} T'$, compatible with $g_a$ and $g_b$ in the sense that the restrictions $U_a \cap U_b \to O_a(U_a \cap U_b)$ and $U_a \cap U_b \to O_b(U_a \cap U_b)$ induced by $g_a$, $g_b$ exist and are matched by $\varphi_{ab}$, and satisfying $\varphi_{ab}^{-1}(O_b(W)) = O_a(W)$ after restriction to the overlap pieces; and, for each strictly increasing triple $r = (a<b<c)$ in $\iota$, writing $W_r = U_a \cap U_b \cap U_c$, isomorphisms $\rho^{ab}_r, \rho^{bc}_r, \rho^{ac}_r$ between the corresponding $O$-pieces of $W_r$ that are compatible with $\varphi_{ab}, \varphi_{bc}, \varphi_{ac}$ under the inclusions of opens, and satisfy the cocycle identity $\rho^{ac}_r = \rho^{ab}_r$ followed by $\rho^{bc}_r$. Then there exist a scheme $X$, a smooth morphism $f_X \colon X \to \operatorname{Spec} T'$, a morphism $g_X \colon A_0 \to X$ making the square with $f_0$, $f_X$ and $\operatorname{Spec}\pi$ cartesian, and morphisms $\iota_a \colon Y_a \to X$ which are open immersions, satisfy $\iota_a$ followed by $f_X$ equals $q_a$, have images covering $X$ set-theoretically, satisfy $g_a$ followed by $\iota_a$ equals the inclusion $U_a \hookrightarrow A_0$ followed by $g_X$, and agree on overlaps: for $a < b$, the inclusion $O_a(U_a \cap U_b) \hookrightarrow Y_a$ followed by $\iota_a$ equals $\varphi_{ab}$ followed by the inclusion $O_b(U_a \cap U_b) \hookrightarrow Y_b$ followed by $\iota_b$.
--
--   This is the gluing step for smooth lifts: local smooth lifts of the charts of $A_0$ along $\operatorname{Spec} T' \to \operatorname{Spec} T$, together with isomorphisms over the pairwise overlaps satisfying the cocycle condition over triple overlaps, are assembled into a single smooth lift of $A_0$. It is used in the construction of smooth lifts of abelian schemes via the property bundle formalism, where the overlap data are produced by deformation-theoretic arguments chart by chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_smooth_isPullback_of_local_lifts_of_overlap_isos.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_smooth_isPullback_of_local_lifts_of_overlap_isos
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (𝒰 : A₀.OrderedAffineCover)

    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)
    (hcoc : ∀ r : 𝒰.Idx 2, (ρac r).hom = (ρab r).hom ≫ (ρbc r).hom) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of T')) (_ : Smooth fX) (gX : A₀ ⟶ X)
      (_ : IsPullback gX f₀ fX (Spec.map (CommRingCat.ofHom π)))
      (ιY : ∀ a, Y a ⟶ X),
      (∀ a, IsOpenImmersion (ιY a)) ∧
      (∀ a, ιY a ≫ fX = q a) ∧
      (∀ x : X, ∃ (a : 𝒰.ι) (y : Y a), (ιY a).base y = x) ∧
      (∀ a, g a ≫ ιY a = (𝒰.U a).ι ≫ gX) ∧
      (∀ (a b : 𝒰.ι) (h : a < b),
        (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ ιY a = (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ ιY b) := by sorry
