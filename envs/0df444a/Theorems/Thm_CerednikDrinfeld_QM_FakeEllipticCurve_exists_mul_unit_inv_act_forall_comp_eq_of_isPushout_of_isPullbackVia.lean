-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/25bb9dc8-67c7-5b02-86da-8dc4432b59b7
-- title:
--   Glued group law and Λ-action on a pushout of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B,B',B''$ be commutative rings and $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ surjective ring homomorphisms with nilpotent kernels, and write $P =$ `pullbackRing φ' φ''` for the subring of $B' \times B''$ on which the two composites to $B$ agree, with its two projections `pullbackFst φ' φ''`, `pullbackSnd φ' φ''`. Let $E'$, $E''$, $E_B$ be fake elliptic curves of level $N$ with $\Lambda$-action over $B'$, $B''$, $B$ respectively, and let $h' : E_B.A \to E'.A$, $h'' : E_B.A \to E''.A$ exhibit $E_B$ as the pullback of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the sense of `IsPullbackVia`: each square of structure morphisms over $\operatorname{Spec}$ of the relevant ring is cartesian, the relative group laws are compatible on $T$-valued points, the $\Lambda$-actions commute with $h'$ resp. $h''$, and points factoring through the level structure of the source have images factoring through that of the target. Let $f : X \to \operatorname{Spec} P$ be a flat morphism of schemes, and $k' : E'.A \to X$, $k'' : E''.A \to X$ morphisms making the squares formed with $E'.f$, $f$ and $\operatorname{Spec}$ of `pullbackFst φ' φ''`, resp. $E''.f$, $f$ and $\operatorname{Spec}$ of `pullbackSnd φ' φ''`, cartesian, such that $h'$ followed by $k'$ equals $h''$ followed by $k''$ and this square is a pushout. The conclusion asserts the existence of morphisms $m : X \times_{\operatorname{Spec} P} X \to X$, $e : \operatorname{Spec} P \to X$, $\iota : X \to X$ and $\mathrm{act}(x) : X \to X$ for $x \in \Lambda$, all over $\operatorname{Spec} P$ (that is, $m$ followed by $f$ equals the first projection followed by $f$, $e$ is a section of $f$, and $\iota$ and each $\mathrm{act}(x)$ commute with $f$), satisfying: on $T$-valued points over any $t' : T \to \operatorname{Spec} P$, $m$ is associative, has $t'$ followed by $e$ as two-sided unit, satisfies $m(x\iota, x) = t' \circ e$ and is commutative; $\mathrm{act}$ sends $1 \in \Lambda$ (when it lies in $\Lambda$) to $\mathrm{id}_X$, satisfies $\mathrm{act}(xy) = \mathrm{act}(x) \circ \mathrm{act}(y)$ in diagrammatic order, is an endomorphism of $m$ on points, and satisfies $\mathrm{act}(x+y)$ on a point equals $m$ applied to its images under $\mathrm{act}(x)$ and $\mathrm{act}(y)$; and finally $k'$ carries the group law, unit, inverse and $\Lambda$-action of $E'$ to $m$, $e$, $\iota$ and $\mathrm{act}$, and likewise $k''$ for $E''$.
--
--   This is the descent of the group structure and quaternionic multiplication along a pushout of total spaces corresponding to a fibre product $B' \times_B B''$ of rings with nilpotent kernels, the standard gluing step in Schlessinger-style deformation theory for the moduli of fake elliptic curves. It is used in the construction of a fake elliptic curve over $B' \times_B B''$ pulling back to the given ones, i.e. in the verification that the moduli functor commutes with such fibre products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
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
    ∃ (m : pullback f f ⟶ X) (e : Spec (CommRingCat.of (pullbackRing φ' φ'')) ⟶ X) (ι : X ⟶ X) (act : ↥Λ → (X ⟶ X))
      (hm : m ≫ f = pullback.fst f f ≫ f) (he : e ≫ f = 𝟙 _) (hι : ι ≫ f = f)
      (act_over : ∀ x : ↥Λ, act x ≫ f = f),

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
          pullback.lift (P.1 ≫ act x) (P.1 ≫ act y) (by rw [Category.assoc, act_over, Category.assoc, act_over]) ≫ m) ∧

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ k' =
          pullback.lift (P.1 ≫ k') (Q.1 ≫ k')
            (by simp only [Category.assoc]; rw [hk'.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')),
        (E'.L.one t').1 ≫ k' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P : SchemeHomOver t' E'.f),
        (E'.L.inv t' P).1 ≫ k' = (P.1 ≫ k') ≫ ι) ∧
      (∀ x : ↥Λ, E'.act x ≫ k' = k' ≫ act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P Q : SchemeHomOver t' E''.f),
        (E''.L.mul t' P Q).1 ≫ k'' =
          pullback.lift (P.1 ≫ k'') (Q.1 ≫ k'')
            (by simp only [Category.assoc]; rw [hk''.w, ← Category.assoc, P.2, ← Category.assoc, Q.2]) ≫ m) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')),
        (E''.L.one t').1 ≫ k'' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P : SchemeHomOver t' E''.f),
        (E''.L.inv t' P).1 ≫ k'' = (P.1 ≫ k'') ≫ ι) ∧
      (∀ x : ↥Λ, E''.act x ≫ k'' = k'' ≫ act x) := by sorry
