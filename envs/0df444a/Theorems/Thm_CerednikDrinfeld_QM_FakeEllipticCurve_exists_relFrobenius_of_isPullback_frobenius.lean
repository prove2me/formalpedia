-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_relFrobenius_of_isPullback_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/5e3b4902-def9-53bd-b893-3cc6ec3af4e6
-- title:
--   Relative Frobenius into the Frobenius twist of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a subgroup $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a field $k$ of characteristic a prime $\ell$, and two objects $E$, $E_\ell$ of type `FakeEllipticCurve Λ N k` (abelian schemes $f$ over $\operatorname{Spec} k$ with a relative group law, a $\Lambda$-action `act` and a level datum $\mathrm{lev} : C \to A$). Assume given $\mathrm{pr} : E_\ell.A \to E.A$ such that the square formed by $\mathrm{pr}$, $E_\ell.f$, $E.f$ and $\operatorname{Spec}$ of the $\ell$-power map of $k$ is cartesian; that $\mathrm{pr}$ carries products of $T$-points of $E_\ell$ to products of their images as points of $E$ over the twisted base (`pr_mul`); that $\mathrm{pr}$ intertwines the two $\Lambda$-actions; that a $T$-point of $E_\ell$ factors through $E_\ell.\mathrm{lev}$ if and only if its image under $\mathrm{pr}$ factors through $E.\mathrm{lev}$ (`pr_lev` and `pr_lev'`); and that $\ell = 0$ in $\Gamma(E.A,\top)$. Then there exist $F : E.A \to E_\ell.A$ with $F \mathbin{;} E_\ell.f = E.f$ such that $F$ followed by $\mathrm{pr}$ is the absolute $\ell$-power Frobenius `E.A.frobenius ℓ 1` of $E.A$; consequently, for every commutative ring $B$ of characteristic $\ell$ and every $x : \operatorname{Spec} B \to E.A$, one has $x \mathbin{;} F \mathbin{;} \mathrm{pr} = \operatorname{Spec}(\mathrm{frobenius}\,B\,\ell) \mathbin{;} x$; moreover post-composition with $F$ is a homomorphism for the group laws on $T$-points, satisfies $E.\mathrm{act}(x) \mathbin{;} F = F \mathbin{;} E_\ell.\mathrm{act}(x)$ for all $x \in \Lambda$, and sends $T$-points factoring through $E.\mathrm{lev}$ to $T$-points factoring through $E_\ell.\mathrm{lev}$.
--
--   This is the existence of the relative Frobenius $F : A \to A^{(\ell)}$ of a fake elliptic curve in characteristic $\ell$, together with its compatibility with the group law, the quaternionic action and the level structure. It is used in the construction of the Frobenius–Verschiebung pair for fake elliptic curves at primes not dividing the relevant level, in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_relFrobenius_of_isPullback_frobenius.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_relFrobenius_of_isPullback_frobenius
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
    (hA : (ℓ : Γ(E.A, ⊤)) = 0) :
    ∃ (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f),
      F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA ∧
      (∀ (B : Type u) [CommRing B] [CharP B ℓ] (x : Spec (CommRingCat.of B) ⟶ E.A),
        x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) ≫ x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P)) := by sorry
