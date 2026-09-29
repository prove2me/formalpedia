-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_transitions_any_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9a1b683b-2180-5aa1-9509-275e3998d8f1
-- title:
--   Overlap transitions for arbitrary ordered pairs of indices
-- statement:
--   Let $A_0$ be a scheme and $\mathcal{U}$ an ordered affine cover of it, i.e. a finite linearly ordered index type $\mathcal{U}.\iota$ together with opens $\mathcal{U}.U_a \subseteq A_0$ that are affine and satisfy $\bigsqcup_a \mathcal{U}.U_a = \top$. Let $T'$ be a commutative ring, and suppose given for each index $a$ a scheme $Y_a$, a morphism $q_a \colon Y_a \to \operatorname{Spec} T'$, a morphism $g_a \colon \mathcal{U}.U_a \to Y_a$ from the open subscheme $\mathcal{U}.U_a$, and a monotone map $O_a$ from the opens of $A_0$ to the opens of $Y_a$. Assume given, for each strictly increasing pair $a < b$, an isomorphism of schemes $\varphi_{ab} \colon O_a(\mathcal{U}.U_a \cap \mathcal{U}.U_b) \cong O_b(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ such that: (i) $\varphi_{ab}$ followed by the open immersion of $O_b(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ into $Y_b$ and then $q_b$ equals the open immersion of $O_a(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ followed by $q_a$; (ii) there exist morphisms $\gamma$ from $\mathcal{U}.U_a \cap \mathcal{U}.U_b$ into $O_a(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ and $\gamma'$ into $O_b(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ whose composites with the respective open immersions are the restrictions of $g_a$ and $g_b$ along the inclusions of the intersection, and with $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$; (iii) for every open $W$ of $A_0$, the preimage under $\varphi_{ab}$ of the preimage of $O_b(W)$ in $O_b(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$ equals the preimage of $O_a(W)$ in $O_a(\mathcal{U}.U_a \cap \mathcal{U}.U_b)$. The conclusion asserts the existence of isomorphisms $\Phi_{a,b,W} \colon O_a(W) \cong O_b(W)$ for all indices $a,b$ (not merely $a<b$) and all opens $W$ of $A_0$ with $W \leq \mathcal{U}.U_a$ and $W \leq \mathcal{U}.U_b$, satisfying: compatibility with the structure morphisms to $\operatorname{Spec} T'$ as in (i); the property that any $\gamma \colon W \to O_a(W)$ and $\gamma' \colon W \to O_b(W)$ whose composites with the open immersions are the restrictions of $g_a$ and $g_b$ satisfy $\gamma$ followed by $\Phi_{a,b,W}$ equal to $\gamma'$; naturality in $W$, namely for $W' \leq W$ (both below $\mathcal{U}.U_a$ and $\mathcal{U}.U_b$) that $\Phi_{a,b,W'}$ followed by the inclusion $O_b(W') \to O_b(W)$ equals the inclusion $O_a(W') \to O_a(W)$ followed by $\Phi_{a,b,W}$; reflexivity $\Phi_{a,a,W} = \mathrm{id}$ (for any two proofs of $W \leq \mathcal{U}.U_a$); symmetry, $\Phi_{a,b,W}$ followed by $\Phi_{b,a,W}$ equal to the identity; and agreement with the given data, $\Phi_{a,b,\mathcal{U}.U_a \cap \mathcal{U}.U_b} = \varphi_{ab}$ whenever $a<b$.
--
--   This packages the transition data of a family of local lifts over an ordered affine cover into a groupoid-like system indexed by arbitrary ordered pairs and arbitrary opens, as is needed when the index map of a refining cover fails to be monotone. It is used in the construction of the two-cocycle obstruction attached to a small extension, via [`AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom`](thm.html#AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom), and rests on the restriction of an isomorphism of open subschemes to smaller opens with matching preimages, [`AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq`](thm.html#AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_transitions_any_pair
    {A₀ : Scheme.{u}} (𝒰 : A₀.OrderedAffineCover)
    {T' : Type u} [CommRing T']
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T'))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (O : ∀ a, A₀.Opens → (Y a).Opens) (hOm : ∀ a, Monotone (O a))
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
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W) :
    ∃ Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)),
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
        (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a) ∧
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
        (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
        γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ') ∧
      (∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
        (hWW : W' ≤ W),
        (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom) ∧
      (∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _) ∧
      (∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
        (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _) ∧
      (∀ (a b : 𝒰.ι) (h : a < b),
        (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom) := by sorry
