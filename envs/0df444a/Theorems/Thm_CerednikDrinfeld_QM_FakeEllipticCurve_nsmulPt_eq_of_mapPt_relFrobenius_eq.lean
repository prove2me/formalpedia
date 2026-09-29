-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_of_mapPt_relFrobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/122651ed-449f-59a9-81b9-4699c1f8937e
-- title:
--   Multiplication by ℓ coequalises the kernel pair of Frobenius
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a field $k$ and a prime $\ell$ with $\operatorname{char} k = \ell$. Let $E$ and $E_\ell$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, i.e. each consists of a scheme $A$ smooth and proper over $\operatorname{Spec} k$ with connected fibres of dimension $2$, a commutative relative group law on its functor of points, an action of $\Lambda$ by endomorphisms compatible with that law and with the trace condition, and level data $\mathrm{lev} : C \to A$. Assume given $pr : E_\ell.A \to E.A$ making the square with the structure morphisms and $\operatorname{Spec}$ of the $\ell$-power map of $k$ cartesian, so that $E_\ell$ is the Frobenius base change of $E$; assume $pr$ is compatible with the group laws in the semilinear sense (for every $T$, every $t' : T \to \operatorname{Spec} k$ and points $P,Q$ of $E_\ell$ over $t'$, composing $E_\ell.L.\mathrm{mul}\,t'\,P\,Q$ with $pr$ gives $E.L.\mathrm{mul}$ of $P \cdot pr$ and $Q \cdot pr$ over $t'$ followed by the Frobenius of $k$), that $E_\ell.\mathrm{act}\,x$ followed by $pr$ equals $pr$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$, and that a point $P$ of $E_\ell$ factors through $E_\ell.\mathrm{lev}$ if and only if $P.1 \circ pr$ factors through $E.\mathrm{lev}$ (both implications assumed). Assume $\ell$ vanishes in $\Gamma(E.A,\top)$, and let $F : E.A \to E_\ell.A$ be a morphism over $\operatorname{Spec} k$ with $F$ followed by $pr$ the absolute Frobenius `E.A.frobenius` (identity on spaces, $\ell$-th power on sections), which is a homomorphism on points: $F$-pushforward of $E.L.\mathrm{mul}\,t\,P\,Q$ equals $E_\ell.L.\mathrm{mul}\,t$ of the pushforwards. Then for every scheme $T$, every $t : T \to \operatorname{Spec} k$ and all $T$-points $g_1, g_2$ of $E.A$ over $t$, if $g_1 \circ F = g_2 \circ F$ (equality of pushed points) then the $\ell$-fold iterates $\mathrm{nsmulPt}\,E.L\,t\,\ell\,g_1$ and $\mathrm{nsmulPt}\,E.L\,t\,\ell\,g_2$ of the group law agree.
--
--   This is the functor-of-points form of the statement that multiplication by $\ell$ kills the kernel of the relative Frobenius of an abelian scheme in characteristic $\ell$, the consequence of the identity $V \circ F = [\ell]$, here for fake elliptic curves with quaternionic action and level structure. It is used in the construction of a Verschiebung for the relative Frobenius of such a curve, in [`CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_of_mapPt_relFrobenius_eq
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
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (g₁ g₂ : SchemeHomOver t E.f)
    (h : mapPt F F_over g₁ = mapPt F F_over g₂) :
    nsmulPt E.L t ℓ g₁ = nsmulPt E.L t ℓ g₂ := by sorry
