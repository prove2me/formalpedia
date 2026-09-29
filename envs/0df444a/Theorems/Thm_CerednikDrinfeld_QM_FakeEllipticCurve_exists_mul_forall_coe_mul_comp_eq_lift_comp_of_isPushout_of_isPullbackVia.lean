-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_forall_coe_mul_comp_eq_lift_comp_of_isPushout_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_forall_coe_mul_comp_eq_lift_comp_of_isPushout_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/182585f2-3b5f-5c06-8606-bdb0f799c273
-- title:
--   Gluing the multiplication morphism over a pushout of total spaces
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and $N \in \mathbb{N}$; these are the data carried by the structure `FakeEllipticCurve`, whose objects over a commutative ring $S$ consist of a scheme $A$ over $\operatorname{Spec} S$ with a commutative relative group law, an abelian-scheme property bundle, fibres of dimension $2$, an action of $\Lambda$ compatible with the group law and satisfying the trace condition, and the level data. Let $B$, $B'$, $B''$ be commutative rings and $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ surjective ring homomorphisms with nilpotent kernels, and write $P = \{(x,y) \in B' \times B'' : \varphi'(x) = \varphi''(y)\}$ for `pullbackRing`, with its two projections `pullbackFst`, `pullbackSnd`. Let $E'$, $E''$, $E_B$ be fake elliptic curves of the given type over $B'$, $B''$, $B$ respectively, and let $h' : E_B.A \to E'.A$, $h'' : E_B.A \to E''.A$ exhibit $E_B$ as the base change of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the sense of `IsPullbackVia`: the square formed by $h'$, the structure morphisms and $\operatorname{Spec}(\varphi')$ is cartesian, $h'$ carries the group law of $E_B$ to that of $E'$ on points over any base, commutes with the $\Lambda$-actions, and sends points factoring through the level morphism of $E_B$ to points factoring through that of $E'$ (similarly for $h''$ and $\varphi''$). Let $f : X \to \operatorname{Spec} P$ be a flat morphism of schemes and let $k' : E'.A \to X$, $k'' : E''.A \to X$ be morphisms making the squares over $\operatorname{Spec}(\mathtt{pullbackFst})$ and $\operatorname{Spec}(\mathtt{pullbackSnd})$ cartesian, so that $E'.A$ and $E''.A$ are the restrictions of $X$ to $\operatorname{Spec} B'$ and $\operatorname{Spec} B''$. Assume $h'$ followed by $k'$ equals $h''$ followed by $k''$, and that this square is a pushout of schemes. Then there is a morphism $m : X \times_{\operatorname{Spec} P} X \to X$ with $m$ followed by $f$ equal to the first projection followed by $f$, such that for every scheme $T$, every $t' : T \to \operatorname{Spec} B'$ and all $T$-points $P,Q$ of $E'.A$ over $t'$, the product $E'.L.\mathrm{mul}\,t'\,P\,Q$ followed by $k'$ equals the morphism $T \to X \times_{\operatorname{Spec} P} X$ with components $P$ followed by $k'$ and $Q$ followed by $k'$, followed by $m$; and the same identity holds for $E''$, $\operatorname{Spec} B''$ and $k''$.
--
--   This is the gluing step which produces a single multiplication morphism on the total space $X$ over the fibre-product ring $P = B' \times_B B''$ out of the group laws of the two fake elliptic curves $E'$ and $E''$ that $X$ restricts to, using flatness of $f$ and the pushout property; products of cartesian squares being cartesian, $X \times_{\operatorname{Spec} P} X$ is again a pushout of the corresponding products. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia), which assembles multiplication, unit, inverse and $\Lambda$-action into a fake elliptic curve over $P$, the Schlessinger-type gluing needed for the deformation-theoretic moduli arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_forall_coe_mul_comp_eq_lift_comp_of_isPushout_of_isPullbackVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_forall_coe_mul_comp_eq_lift_comp_of_isPushout_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    (E' : FakeEllipticCurve Λ N B') (E'' : FakeEllipticCurve Λ N B'') (EB : FakeEllipticCurve Λ N B)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'')
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (k' : E'.A ⟶ X) (hk' : CategoryTheory.IsPullback k' E'.f f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : E''.A ⟶ X) (hk'' : CategoryTheory.IsPullback k'' E''.f f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (hcomm : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'') :
    ∃ (m : pullback f f ⟶ X) (hm : m ≫ f = pullback.fst f f ≫ f),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ k' =
          pullback.lift (P.1 ≫ k') (Q.1 ≫ k')
            (by simp only [Category.assoc]; rw [hk'.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P Q : SchemeHomOver t' E''.f),
        (E''.L.mul t' P Q).1 ≫ k'' =
          pullback.lift (P.1 ≫ k'') (Q.1 ≫ k'')
            (by simp only [Category.assoc]; rw [hk''.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) := by sorry
