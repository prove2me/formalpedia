-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/daf45b55-a944-5961-b6db-e486cc523d73
-- title:
--   Frobenius–Verschiebung datum from a finite flat relative Frobenius
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $\ell$, and a field $k$ of characteristic $\ell$ which is algebraically closed, with $\ell \nmid N$. Let $E$ and $E_\ell$ be fake elliptic curves over $k$ of level $N$ with $\Lambda$-action, i.e. objects of `FakeEllipticCurve Λ N k`, each consisting of a scheme with a structure morphism to $\operatorname{Spec} k$, a commutative relative group law on its functor of points, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over $k$ compatible with the group law and with a trace condition, and a level scheme with its morphism `lev`. Assume given $\mathrm{pr} : E_\ell.A \to E.A$ making the square with the structure morphisms and $\operatorname{Spec}$ of the $\ell$-power Frobenius of $k$ cartesian, such that $\mathrm{pr}$ carries the group law of $E_\ell$ to that of $E$ after twisting the base point by Frobenius, commutes with the $\Lambda$-actions, and satisfies both implications relating points of $E_\ell$ factoring through $E_\ell.\mathrm{lev}$ and points whose composite with $\mathrm{pr}$ factors through $E.\mathrm{lev}$. Assume $\ell$ vanishes in $\Gamma(E.A,\top)$, and let $F : E.A \to E_\ell.A$ be a morphism over $\operatorname{Spec} k$ with $F$ followed by $\mathrm{pr}$ equal to the absolute $\ell$-power Frobenius `E.A.frobenius ℓ 1` of $E.A$, such that $F$ is a homomorphism for the group laws on points, commutes with the $\Lambda$-actions, and sends points factoring through $E.\mathrm{lev}$ to points factoring through $E_\ell.\mathrm{lev}$; assume moreover that $F$ is flat, surjective and finite. Then `HasFrobeniusVerschiebung ℓ E Eℓ` holds: the structure `FrobeniusVerschiebungData ℓ E Eℓ` is nonempty, i.e. there are a cartesian projection $\mathrm{pr}$ with the compatibilities above and morphisms $F : E.A \to E_\ell.A$, $V : E_\ell.A \to E.A$ over $\operatorname{Spec} k$, each a homomorphism for the group laws, $\Lambda$-equivariant and level-compatible, satisfying the remaining conditions recorded in that structure.
--
--   This is the existence of the Verschiebung for a fake elliptic curve in characteristic $\ell$: once the relative Frobenius $F$ is known to be finite, flat and surjective, multiplication by $\ell$ descends along $F$ and yields a dual morphism $V$, producing a full Frobenius–Verschiebung datum for the pair $(E, E_\ell)$. It is the final step of `exists_hasFrobeniusVerschiebung_of_prime_not_dvd`, and draws on the description of $\ell$-torsion and of level points under relative Frobenius supplied by `nsmulPt_eq_of_mapPt_relFrobenius_eq` and `existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k)
    (pr : Eℓ.A ⟶ E.A)
    (pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius k ℓ))))
    (pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Eℓ.f),
      (Eℓ.L.mul t' P Q).1 ≫ pr =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
          ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1)
    (pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x)
    (pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr)
    (pr_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr) → FactorsThrough Eℓ.lev P)
    (hA : (ℓ : Γ(E.A, ⊤)) = 0)
    (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f) (F_pr : F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA)
    (F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q))
    (F_act : ∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x)
    (F_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P))
    [IsAlgClosed k] (hℓN : ¬ ℓ ∣ N) [Flat F] [Surjective F] [IsFinite F] :
    HasFrobeniusVerschiebung ℓ E Eℓ := by sorry
