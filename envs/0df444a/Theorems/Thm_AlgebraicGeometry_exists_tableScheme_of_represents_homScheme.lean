-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme
-- name    : AlgebraicGeometry.exists_tableScheme_of_represents_homScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/4c7b55fe-97f4-56b1-a38b-c22c0b355d52
-- title:
--   Existence of the table scheme of endomorphism quadruples
-- statement:
--   Let $R$ be a commutative ring, let $f : A \to \operatorname{Spec} R$ be a scheme over $R$ and let $L$ be a relative group law on $f$ — a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $t : T \to \operatorname{Spec} R$, natural in $T$ — assumed commutative ($hc$). Fix integers $c_{jkl}$ and $u_l$ indexed by $j,k,l \in \mathrm{Fin}(2\cdot 2)$. Let $\pi_H : H \to \operatorname{Spec} R$ together with a rule $\mathrm{pt}$ assigning, to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and every $\varphi : A\times_{\operatorname{Spec} R}\operatorname{Spec} S' \to A$ with $\varphi \circ f = s \circ \mathrm{pr}_2$, a point of $H$ over $s$, satisfy: ($hHnat$) compatibility of $\mathrm{pt}$ with base change along ring maps $\psi : S' \to S''$; ($hHsurj$) every point of $H$ over $s$ is $\mathrm{pt}\,S'\,s\,\varphi$ for some $\varphi$ as above which is multiplicative, i.e. for all $T$, $t' : T \to \operatorname{Spec} S'$ and all points $P,Q$ of $A$ over $t' \circ s$, composing the $L$-product of $P$ and $Q$ with $\varphi$ equals the $L$-product of the composites; ($hHinj$) two such multiplicative $\varphi, \varphi'$ with the same $\mathrm{pt}$-value are equal; and $\pi_H$ is separated, locally of finite type and locally of finite presentation. Then there exist $E$, $\pi_E : E \to \operatorname{Spec} R$ and morphisms $p_j : E \to H$ over $\operatorname{Spec} R$ ($j \in \mathrm{Fin}(2\cdot 2)$) such that $\pi_E$ is separated, locally of finite type and locally of finite presentation; for every family of opens $U_j \subseteq H$ with each $U_j$ closed and each $U_j \hookrightarrow H \to \operatorname{Spec} R$ quasi-compact, the open $\bigcap_j p_j^{-1}(U_j)$ of $E$ is closed and quasi-compact over $\operatorname{Spec} R$; a point of $E$ over $s$ is determined by its images under the $p_j$; and for every $S'$, every $s$ and every family $\varphi_j$ of morphisms over $s$ as above, all multiplicative in the sense stated, there is a point $z$ of $E$ over $s$ with $z \circ p_j = \mathrm{pt}\,S'\,s\,\varphi_j$ for all $j$ if and only if, in the commutative group of points of $A$ over $s \circ \mathrm{pr}_2$ supplied by $L$ and $hc$, one has $\prod_l \varphi_l^{\,c_{jkl}} = \varphi_j \circ \varphi_k$ (composition of $\varphi_k$, lifted to the fibre product, with $\varphi_j$) for all $j,k$, and $\prod_l \varphi_l^{\,u_l} = \mathrm{pr}_1$.
--
--   This constructs the scheme parametrising quadruples of endomorphisms of $A$ (as a relative group) obeying the multiplication table $\beta_j\beta_k = \sum_l c_{jkl}\beta_l$, $1 = \sum_l u_l\beta_l$ of a rank-four order, starting from a scheme representing the endomorphisms on affine points; the properties listed (separatedness, finite type, finite presentation, and closedness plus quasi-compactness of intersections of preimages) are those inherited from a closed immersion into the fourfold fibre power of $H$. It is used in the Čerednik–Drinfeld part of the development, to represent actions of a quaternionic lattice on an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.exists_tableScheme_of_represents_homScheme
    {R : Type} [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f s ⟶ A), φ ≫ f = pullback.snd f s ≫ s → SchemeHomOver s πH)
    (hHnat : (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1))
    (hHsurj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x))
    (hHinj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ φ' : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hφ' : φ' ≫ f = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'))
    (hHsep : IsSeparated πH) (hHlft : LocallyOfFiniteType πH) (hHlfp : LocallyOfFinitePresentation πH) :
    ∃ (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R)) (p : Fin (2 * 2) → (E ⟶ H)),
      (∀ j, p j ≫ πH = πE) ∧ IsSeparated πE ∧ LocallyOfFiniteType πE ∧ LocallyOfFinitePresentation πE ∧
      (∀ U : Fin (2 * 2) → H.Opens, (∀ j, IsClosed ((U j : Set H))) → (∀ j, QuasiCompact ((U j).ι ≫ πH)) →
        IsClosed ((⨅ j, (p j) ⁻¹ᵁ (U j) : E.Opens) : Set E) ∧ QuasiCompact ((⨅ j, (p j) ⁻¹ᵁ (U j)).ι ≫ πE)) ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (z z' : SchemeHomOver s πE),
        (∀ j, z.1 ≫ p j = z'.1 ≫ p j) → z = z') ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ : Fin (2 * 2) → (pullback f s ⟶ A)) (hφ : ∀ j, φ j ≫ f = pullback.snd f s ≫ s),
        (∀ j, (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ j =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩).1)) →
        ((∃ z : SchemeHomOver s πE, ∀ j, z.1 ≫ p j = (pt S' s (φ j) (hφ j)).1) ↔
          (letI := L.pointCommGroup hc (pullback.snd f s ≫ s)
           (∀ j k : Fin (2 * 2),
              (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c j k l)) =
                ⟨pullback.lift (φ k) (pullback.snd f s) (hφ k) ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩) ∧
           (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l)) = ⟨pullback.fst f s, pullback.condition⟩))) := by sorry
