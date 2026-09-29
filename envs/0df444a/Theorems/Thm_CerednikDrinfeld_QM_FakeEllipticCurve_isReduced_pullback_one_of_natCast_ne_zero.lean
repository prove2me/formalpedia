-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/cbe309aa-0e86-5e7a-a160-3a52984e6146
-- title:
--   Kernel of an isogeny of fake elliptic curves is reduced and finite
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$, and let $k$ be an algebraically closed field. Let $E$ and $E'$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, each consisting of a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$ on $T$-points (morphisms $T \to E.A$ over a given $T \to \operatorname{Spec} k$), the smooth, proper, connected-fibre bundle of properties, fibres of topological Krull dimension $2$, and an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ compatible with the group law and with the trace condition. Let $\varphi : E.A \to E'.A$ be a morphism over $\operatorname{Spec} k$ (that is, $\varphi$ followed by $E'.f$ equals $E.f$) which is additive on $T$-points for all base schemes $T$, and which is $\Lambda$-equivariant in the sense that $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}\,x$ for every $x \in \Lambda$. Let $\psi : E'.A \to E.A$ be a morphism over $\operatorname{Spec} k$ and $n$ a natural number with $n \neq 0$ in $k$, such that on $T$-points the composites $\psi \circ \varphi$ and $\varphi \circ \psi$ are the $n$-fold iterated sum (defined from the unit by repeated multiplication) on $E$ and on $E'$ respectively. Then the fibre product of $\varphi$ with the unit $\operatorname{Spec} k \to E'.A$ of $E'.L$ at the identity base morphism is a reduced scheme, and the first projection of that pullback followed by $E.f$ is locally of finite type and finite.
--
--   This is the scheme-theoretic statement that the kernel of an isogeny of fake elliptic curves whose degree witness $n$ is invertible in the base field is a finite reduced (hence étale) $k$-scheme, obtained by viewing it as a closed subscheme of the $n$-torsion. It is the bridge from kernel conditions checked on points to the scheme-theoretic hypotheses needed by the quotient property of isogenies, and is used in the identification of Hecke neighbours with level isogenies and in the uniqueness statements for sections with prescribed $n$-torsion behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_pullback_one_of_natCast_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_pullback_one_of_natCast_ne_zero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k]
    (E E' : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x)
    (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (n : ℕ) (hnk : (n : k) ≠ 0)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t n P)
    (hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t n Q) :
    IsReduced (Limits.pullback φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1) ∧
      LocallyOfFiniteType (Limits.pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f) ∧
      IsFinite (Limits.pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f) := by sorry
