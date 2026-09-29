-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/fa72040f-5806-59da-96f6-0a8d5f5b4b7c
-- title:
--   Geometric fibres of the fine-to-coarse map are G-orbits
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, has $\mathbb{Q}$-span the whole algebra, and is finitely generated; fix $N, n \in \mathbb{N}$ and a commutative base ring $B$. Let $f : \mathcal{X} \to \operatorname{Spec} B$ together with a rule $\mathrm{pt}$, assigning to each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and each fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data a morphism $\operatorname{Spec} S \to \mathcal{X}$ over $s$, be a coarse moduli datum in the sense of `IsCoarseModuli` (invariance under isomorphism, compatibility with pullback along ring maps, surjectivity and injectivity on points over algebraically closed fields, and the universal property). Let $f_M : M \to \operatorname{Spec} B$ with a rule $\mathrm{ptF}$ on pairs (fake elliptic curve, full level-$n$ structure) be a fine moduli datum in the sense of `IsFineModuli` (invariance under isomorphism, compatibility with pullback, and bijectivity on $S$-points for every $S$). Let $G$ be a group, $\rho : G \to \operatorname{Aut} M$ a homomorphism and $\chi : G \to \Lambda$ a labelling such that `IsLevelTwistAction` holds: each $\rho(g)$ is a morphism over $\operatorname{Spec} B$, the $\chi(g)$-twist of a full-level object is sent by $\mathrm{ptF}$ to its value composed with $\rho(g)$, and $\chi$ is multiplicative, unital, surjective onto two-sided units and injective, all modulo $n\Lambda$. Let $p : M \to \mathcal{X}$ satisfy $\mathrm{ptF}(S,s,u)$ followed by $p$ equals $\mathrm{pt}(S,s,u_1)$ for all $S$, $s$ and all $u$ with underlying curve $u_1$. Then for every algebraically closed field $k$, every $s : \operatorname{Spec} k \to \operatorname{Spec} B$ and all morphisms $y, y' : \operatorname{Spec} k \to M$ over $s$ with $y$ followed by $p$ equal to $y'$ followed by $p$, there exists $g \in G$ with $y' = \rho(g) \circ y$.
--
--   This is the statement that the geometric fibres of the forgetful map from the fine moduli scheme of fake elliptic curves with full level-$n$ structure to the coarse moduli scheme of fake elliptic curves are single orbits of the level-twisting action of $G$. It is used in the study of the fine moduli scheme of the Čerednik–Drinfeld setting, in particular by [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_of_geometricallyConnected_of_isOpen_of_nonempty_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_of_geometricallyConnected_of_isOpen_of_nonempty_of_isUnit_two_of_isUnit_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsLevelTwistAction.exists_eq_comp_hom_of_comp_eq_of_isAlgClosed_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ} {B : Type} [CommRing B]
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)
    (n : ℕ) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)
    (p : M ⟶ 𝒳)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (y y' : SchemeHomOver s fM) (hyy' : y.1 ≫ p = y'.1 ≫ p) :
    ∃ g : G, y'.1 = y.1 ≫ (ρ g).hom := by sorry
