-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme
-- name    : CerednikDrinfeld.QM.exists_representsLatticeActions_of_represents_homScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f38fff60-3622-532f-ab90-4e9d5a4c2b1d
-- title:
--   Lattice-action scheme from a representing Hom-scheme
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is everything and it is finitely generated; let $\beta$ be a family indexed by a four-element type such that every element of $\Lambda$ is uniquely an integral combination $\sum_j c_j\beta_j$. Let $R$ be a commutative ring, $f : A \to \operatorname{Spec} R$ a morphism of schemes, $L$ a relative group law for $f$ (functorial group structure on $T$-points over $\operatorname{Spec} R$, compatible with base change), assumed commutative, with $f$ satisfying `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, admitting a relative group law), and let $\mathcal{L}$ be a module on $A$ that is invertible (locally isomorphic to the unit module) and satisfies `ClosedImmersionBySections` for $f$, i.e. admits a projective presentation by $N+1$ global sections whose associated morphism to $\operatorname{Proj}$ of the polynomial ring over $R$ is a closed immersion. Let $H$ be a scheme with $\pi_H : H \to \operatorname{Spec} R$ together with a rule $\mathrm{pt}$ assigning, to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and every $\varphi$ from the pullback of $f$ along $s$ to $A$ lying over $s$, a point of $H$ over $s$; it is assumed that $\mathrm{pt}$ is compatible with base change along ring maps $S' \to S''$, that every point of $H$ over $s$ is $\mathrm{pt}$ of some $\varphi$ which is a homomorphism for $L$ (it carries $L$-products of $T$-points to $L$-products, for all $T$ over $\operatorname{Spec} S'$), that two such $L$-homomorphisms with the same $\mathrm{pt}$ coincide, that $\pi_H$ is separated, locally of finite type and locally of finite presentation, and that for every $e \in \mathbb{N}$ there is an open $U \subseteq H$ whose underlying set is closed, with $U \hookrightarrow H$ followed by $\pi_H$ quasi-compact, such that for every $L$-homomorphism $\varphi$ as above the image of $\mathrm{pt}(\varphi)$ lies in $U$ exactly when, for every algebraically closed field $k$ and every ring map $S' \to k$, the geometric-fibre $h^0$ of the tensor product of the pullback of $\mathcal{L}$ along the first projection with the pullback of $\mathcal{L}$ along $\varphi$ equals $e$. The conclusion asserts the existence of a scheme $E$, a morphism $\pi_E : E \to \operatorname{Spec} R$ and a rule $\mathrm{cl}$ which, given a commutative ring $R'$, a ring map $\phi : R \to R'$, a scheme $A'$ over $\operatorname{Spec} R'$ with relative group law $L'$, a morphism $g : A' \to A$ exhibiting $(f',L')$ as the pullback of $(f,L)$ along $\phi$, and a `LatticeAction` of $\Lambda$ on $(f',L')$, returns a point of $E$ over $\operatorname{Spec}\phi$, such that: `RepresentsLatticeActions` holds for $\Lambda$, $L$, $E$, $\pi_E$, $\mathrm{cl}$ (compatibility of $\mathrm{cl}$ with further base change, and surjectivity and injectivity of $\mathrm{cl}$ on lattice actions); $\pi_E$ is separated, locally of finite type and locally of finite presentation; and for every $e$ indexed by the four-element type there is an open $U \subseteq E$ whose underlying set is closed, with the inclusion followed by $\pi_E$ quasi-compact, such that for all $R',\phi,L',g$ as above and every lattice action $X'$, the image of $\mathrm{cl}(X')$ lies in $U$ if and only if for each index $j$, each algebraically closed field $k$ and each ring map $R' \to k$, the geometric-fibre $h^0$ of the tensor product of $g^*\mathcal{L}$ with the pullback of $g^*\mathcal{L}$ along $X'.\mathrm{act}(\beta_j)$ equals $e_j$.
--
--   This is the representability of $\Lambda$-actions on an abelian scheme with commutative group law, in the form that takes as hypothesis the representability of the endomorphisms of the base changes of $(A,L)$ by a Hom-scheme $H$ with quasi-compact degree pieces, and produces a corresponding scheme $E$ classifying actions of the order $\Lambda$, with pieces indexed by the degrees attached to the four basis elements. It feeds the construction of integral models in the Čerednik–Drinfeld part of the argument, being used by [`CerednikDrinfeld.QM.exists_representsLatticeActions_of_closedImmersionBySections_of_topologicalKrullDim`](thm.html#CerednikDrinfeld.QM.exists_representsLatticeActions_of_closedImmersionBySections_of_topologicalKrullDim); the proof passes through the multiplication table of $\beta$ and an auxiliary table scheme inside a fourfold fibre product of $H$ over $\operatorname{Spec} R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme.lean

import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_representsLatticeActions_of_represents_homScheme
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (R : Type) [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
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
    (hHsep : IsSeparated πH) (hHlft : LocallyOfFiniteType πH) (hHlfp : LocallyOfFinitePresentation πH)
    (hHpieces : (∀ e : ℕ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k),
              Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛 ⊗ (Scheme.Modules.pullback φ).obj 𝓛) k sk = e))) :
    ∃ (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
      (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ A), IsGroupPullback φ L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE),
      RepresentsLatticeActions Λ L E πE cl ∧ IsSeparated πE ∧ LocallyOfFiniteType πE ∧ LocallyOfFinitePresentation πE ∧

      (∀ e : Fin (2 * 2) → ℕ, ∃ U : E.Opens, IsClosed (U : Set E) ∧ QuasiCompact (U.ι ≫ πE) ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
          (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L'),
          (Set.range (cl R' φ L' g hg X').1.base ⊆ (U : Set E) ↔
            ∀ (j : Fin (2 * 2)) (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k),
              Scheme.Modules.geomFibreH0Finrank f'
                ((Scheme.Modules.pullback g).obj 𝓛 ⊗
                  (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj 𝓛)) k sk = e j)) := by sorry
