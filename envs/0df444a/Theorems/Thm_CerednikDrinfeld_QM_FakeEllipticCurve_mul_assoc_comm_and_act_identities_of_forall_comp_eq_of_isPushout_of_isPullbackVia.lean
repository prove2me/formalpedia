-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/6f43be5b-3dc1-5814-a342-972993ddd3d0
-- title:
--   Group law and Λ-action axioms over the fibre ring
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ and $N \in \mathbb{N}$. Let $B,B',B''$ be commutative rings and $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ surjective ring homomorphisms whose kernels are nilpotent ideals, let $E'$, $E''$, $E_B$ be fake elliptic curves of level data $(\Lambda,N)$ over $B'$, $B''$, $B$ respectively, and let $h' : E_B.A \to E'.A$, $h'' : E_B.A \to E''.A$ exhibit `IsPullbackVia` for $\varphi'$ and $\varphi''$: each is a pullback square of the structure morphisms along the corresponding $\operatorname{Spec}$ map, compatible with the relative group laws, with the $\Lambda$-actions, and with lifting of points factoring through the level morphism. Let $P = \{(x,y) \in B' \times B'' : \varphi'(x) = \varphi''(y)\}$ be the ring `pullbackRing` $\varphi'\,\varphi''$, and let $f : X \to \operatorname{Spec} P$ be flat, with $k' : E'.A \to X$ and $k'' : E''.A \to X$ pullback squares of $E'.f$, $E''.f$ along the two projections $\operatorname{Spec}$ of `pullbackFst` and `pullbackSnd`; assume $h' \mathbin{\text{then}} k' = h'' \mathbin{\text{then}} k''$ and that this square is a pushout. Assume given morphisms $m : X \times_{\operatorname{Spec} P} X \to X$, $e : \operatorname{Spec} P \to X$, $\iota : X \to X$ and $\mathrm{act} : \Lambda \to \operatorname{End}(X)$, all over $\operatorname{Spec} P$ ($e$ being a section of $f$), whose restrictions along $k'$ and along $k''$ compute the group-law multiplication, unit, inverse and $\Lambda$-action of $E'$ and of $E''$ in the stated pointwise formulas. The conclusion is the conjunction of nine identities: for every scheme $T$, every $t' : T \to \operatorname{Spec} P$ and all $T$-points of $X$ over $t'$, associativity of $m$, the two unit laws for $t' \mathbin{\text{then}} e$, the left inverse law for $\iota$, and commutativity of $m$; together with $\mathrm{act}\langle 1\rangle = \mathrm{id}_X$ when $1 \in \Lambda$, $\mathrm{act}(xy) = \mathrm{act}(y)$ followed by $\mathrm{act}(x)$ for $x,y \in \Lambda$ with $xy \in \Lambda$, compatibility of each $\mathrm{act}(x)$ with $m$ on pairs of points, and $P \mathbin{\text{then}} \mathrm{act}(x+y) = m$ applied to $(P \mathbin{\text{then}} \mathrm{act}(x), P \mathbin{\text{then}} \mathrm{act}(y))$.
--
--   This is the verification step in the construction of a fake elliptic curve over the fibre ring $B' \times_B B''$: once multiplication, unit, inversion and the $\Lambda$-action have been glued over the pushout, all the commutative group-law axioms and the axioms of the quaternionic action hold for the glued data. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia), which produces that data in the first place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.mul_assoc_comm_and_act_identities_of_forall_comp_eq_of_isPushout_of_isPullbackVia
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
    (hcomm : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'')
    (m : pullback f f ⟶ X) (hm : m ≫ f = pullback.fst f f ≫ f)
    (e : Spec (CommRingCat.of (pullbackRing φ' φ'')) ⟶ X) (he : e ≫ f = 𝟙 _)
    (ι : X ⟶ X) (hι : ι ≫ f = f) (act : ↥Λ → (X ⟶ X)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (hmul' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ k' =
          pullback.lift (P.1 ≫ k') (Q.1 ≫ k')
            (by simp only [Category.assoc]; rw [hk'.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')),
        (E'.L.one t').1 ≫ k' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ≫ e)
    (hinv' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P : SchemeHomOver t' E'.f),
        (E'.L.inv t' P).1 ≫ k' = (P.1 ≫ k') ≫ ι)
    (hact' : ∀ x : ↥Λ, E'.act x ≫ k' = k' ≫ act x)
    (hmul'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P Q : SchemeHomOver t' E''.f),
        (E''.L.mul t' P Q).1 ≫ k'' =
          pullback.lift (P.1 ≫ k'') (Q.1 ≫ k'')
            (by simp only [Category.assoc]; rw [hk''.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m)
    (hone'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')),
        (E''.L.one t').1 ≫ k'' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ≫ e)
    (hinv'' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P : SchemeHomOver t' E''.f),
        (E''.L.inv t' P).1 ≫ k'' = (P.1 ≫ k'') ≫ ι)
    (hact'' : ∀ x : ↥Λ, E''.act x ≫ k'' = k'' ≫ act x) :

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x y z : SchemeHomOver t' f),
        pullback.lift (pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) z.1
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, x.2, z.2]) ≫ m =
          pullback.lift x.1 (pullback.lift y.1 z.1 (y.2.trans z.2.symm) ≫ m)
            (by rw [Category.assoc, hm, pullback.lift_fst_assoc, y.2, x.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift (t' ≫ e) x.1 (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift x.1 (t' ≫ e) (by rw [Category.assoc, he, Category.comp_id, x.2]) ≫ m = x.1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x : SchemeHomOver t' f),
        pullback.lift (x.1 ≫ ι) x.1 (by rw [Category.assoc, hι]) ≫ m = t' ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (x y : SchemeHomOver t' f),
        pullback.lift y.1 x.1 (y.2.trans x.2.symm) ≫ m = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧

      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h1⟩ = 𝟙 X) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t' f),
        pullback.lift (P.1 ≫ act x) (Q.1 ≫ act x) (by rw [Category.assoc, act_over, Category.assoc, act_over, P.2, Q.2]) ≫ m =
          (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ m) ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t' f),
        P.1 ≫ act (x + y) =
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) := by sorry
