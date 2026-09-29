-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
-- name    : CerednikDrinfeld.QM.IsFineModuliT.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/1b62dbc8-ec56-5920-91f6-7c4b804bf812
-- title:
--   Geometric fibres of the full-level forgetful map are G-orbits
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, and is finitely generated), naturals $N$, $n$, $\ell$, and a commutative ring $\mathcal{O}$. Suppose given: a scheme $\mathcal{Y}$ with $g : \mathcal{Y} \to \operatorname{Spec}\mathcal{O}$ and an assignment `ptT` sending each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve of level $N$ over $S$ together with an extra level structure at $\ell$ to a morphism $\operatorname{Spec} S \to \mathcal{Y}$ over $s$, such that `IsCoarseModuliT` holds (invariance under isomorphisms of such pairs, compatibility with pullback along ring maps, bijectivity up to isomorphism on points of algebraically closed fields, and the universal property among point assignments with the first two properties); a scheme $M$ over $\operatorname{Spec}\mathcal{O}$ with a point assignment `ptF` for pairs (fake elliptic curve, full level structure of order $n$), a group $G$, a map $\chi : G \to \Lambda$ and $\rho : G \to \operatorname{Aut} M$ satisfying `IsLevelTwistAction` (each $\rho(h)$ lies over the base, $\rho$ realises twisting of full level structures by $\chi(h)$, and $\chi$ is multiplicative, surjective and injective modulo $n\Lambda$ onto the classes invertible modulo $n$); a scheme $M_\ell$ over $\operatorname{Spec}\mathcal{O}$ with a point assignment `ptFℓ` for triples (fake elliptic curve, full level structure of order $n$, extra level structure at $\ell$) satisfying `IsFineModuliT` (invariance under isomorphisms of triples, pullback compatibility, surjectivity on points over every ring, and injectivity up to such an isomorphism); a homomorphism $\rho_\ell : G \to \operatorname{Aut} M_\ell$ for which, whenever $e : u_1.A \cong u'_1.A$ over $S$ exhibits $u'$ as the twist of $u$ by $\chi(h)$ in the sense of `WithFullLevel.IsTwistVia` and $e$ matches the $\ell$-level subschemes $C$, $C'$ (a $T$-point factors through `C.levK` exactly when its image under $e$ factors through `C'.levK`), one has $\mathrm{pt}_{F,\ell}(u',C') = \mathrm{pt}_{F,\ell}(u,C)$ followed by $\rho_\ell(h)$; and a morphism $p_\ell : M_\ell \to \mathcal{Y}$ with $\mathrm{pt}_{F,\ell}(u,C)$ followed by $p_\ell$ equal to $\mathrm{pt}_T\langle u_1, C\rangle$ for all $S$, $s$, $u$, $C$. Then for every algebraically closed field $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec}\mathcal{O}$ and all $y, y' : \operatorname{Spec} k \to M_\ell$ over $s$ with $y$ followed by $p_\ell$ equal to $y'$ followed by $p_\ell$, there exists $h \in G$ with $y' = y$ followed by $\rho_\ell(h)$.
--
--   This is the statement that the morphism forgetting the full level structure from the fine moduli scheme of triples to the coarse moduli scheme of pairs has geometric fibres consisting of single orbits of the level-twisting group $G$, in the presence of an extra level structure at $\ell$. It is used in the construction of the tower of integral models of the Shimura curve, in [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_tower_of_geometricallyConnected_of_isOpen_of_nonempty_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_tower_of_geometricallyConnected_of_isOpen_of_nonempty_of_isUnit_two_of_isUnit_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (n ℓ : ℕ)
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (h𝒴 : IsCoarseModuliT Λ N ℓ 𝒴 g ptT)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ)
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    (G : Type) [Group G] (χ : G → ↥Λ) (ρ : G →* Aut M) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ) (ρℓ : G →* Aut Mℓ)
    (hρℓtw : ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
      (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
        (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom)
    (pℓ : Mℓ ⟶ 𝒴)
    (hpℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel ℓ), (ptFℓ S s u C).1 ≫ pℓ = (ptT S s ⟨u.1, C⟩).1)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (y y' : SchemeHomOver s fMℓ) (hyy' : y.1 ≫ pℓ = y'.1 ≫ pℓ) :
    ∃ g : G, y'.1 = y.1 ≫ (ρℓ g).hom := by sorry
