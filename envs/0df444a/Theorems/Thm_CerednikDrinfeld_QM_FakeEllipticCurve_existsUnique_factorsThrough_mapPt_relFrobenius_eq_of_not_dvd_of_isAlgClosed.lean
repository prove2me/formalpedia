-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/462b9dbb-76e5-5af2-bcc4-d4e5a6a174fc
-- title:
--   Frobenius is bijective on level points when ℓ ∤ N
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $k$ be an algebraically closed field of characteristic a prime $\ell$, and let $E$ and $E_\ell$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, i.e. data consisting of a scheme $A$ over $\operatorname{Spec} k$ with a relative group law, an abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ compatible with the group law and with traces, and a level datum $\mathrm{lev} : C \to A$. Assume given $\mathrm{pr} : E_\ell.A \to E.A$ making the square with the structure morphisms and $\operatorname{Spec}$ of the $\ell$-power map $k \to k$ cartesian, such that $\mathrm{pr}$ carries the group law of $E_\ell$ to that of $E$ on points over any base (hypothesis `pr_mul`), intertwines the $\Lambda$-actions via $E_\ell.\mathrm{act}\,x \mathbin{;} \mathrm{pr} = \mathrm{pr} \mathbin{;} E.\mathrm{act}\,x$, and satisfies: a $T$-point $P$ of $E_\ell.A$ over $t'$ factors through $E_\ell.\mathrm{lev}$ if and only if $P \mathbin{;} \mathrm{pr}$ factors through $E.\mathrm{lev}$ (the two hypotheses `pr_lev`, `pr_lev'`). Assume $\ell$ vanishes in $\Gamma(E.A,\top)$, and let $F : E.A \to E_\ell.A$ be a morphism over $\operatorname{Spec} k$ with $F \mathbin{;} \mathrm{pr}$ equal to the $\ell$-power Frobenius endomorphism of $E.A$ and with $F$ additive on points over any base. If $\ell \nmid N$, then for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} k$ and every $T$-point $Q$ of $E_\ell.A$ over $t$ that factors through $E_\ell.\mathrm{lev}$, there is exactly one $T$-point $P$ of $E.A$ over $t$ which factors through $E.\mathrm{lev}$ and satisfies $P \mathbin{;} F = Q$.
--
--   This is the statement that the relative Frobenius of a fake elliptic curve in characteristic $\ell$ is bijective on points of the level-$N$ subscheme when $\ell \nmid N$, reflecting the étaleness of that subscheme; the proof invokes the reducedness of $E.C$ under $(N : k) \neq 0$. It is used in the construction of Frobenius–Verschiebung data for fake elliptic curves with relative Frobenius, [`CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
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
    (hℓN : ¬ ℓ ∣ N)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eℓ.f) (hQ : FactorsThrough Eℓ.lev Q) :
    ∃! P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt F F_over P = Q := by sorry
