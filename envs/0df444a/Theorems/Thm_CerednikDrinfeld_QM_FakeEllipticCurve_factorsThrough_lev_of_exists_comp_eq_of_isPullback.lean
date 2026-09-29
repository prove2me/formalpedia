-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/49647199-1a23-58da-8431-81a8fe34490a
-- title:
--   Level structures match exactly across a cartesian square
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$ and $E'$ one over $S'$; each consists of a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec}$ of the base, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $T$-points over the base, with the group axioms and compatibility with base change) which is commutative, an abelian-scheme property bundle for $f$ (smooth, proper, connected fibres, a group law existing), two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base that is additive, multiplicative and satisfies the trace condition on tangent spaces, together with a level datum $\mathrm{lev} : C \to A$ whose recorded properties include `lev_closed`, `lev_finite`, `lev_flat`, `lev_finitePresentation` and the fibre-rank normalisation `lev_rank` in terms of $N$. Assume given $g : E'.A \to E.A$ such that the square formed by $g$, $E'.f$, $E.f$ and $\operatorname{Spec}(\varphi)$ is cartesian; that $g$ transports the group law, i.e. for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P,Q$ of $E'.A$ over $t'$ the composite of $E'.L.\mathrm{mul}\,t'\,P\,Q$ with $g$ equals $E.L.\mathrm{mul}$ of the images of $P$ and $Q$ over $t'$ followed by $\operatorname{Spec}(\varphi)$; and the one-directional level clause: whenever a $T$-point $P$ over $t'$ factors through $E'.\mathrm{lev}$, there is $P_0 : T \to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$ followed by $g$. The conclusion is the converse implication: for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and every $T$-point $P$ of $E'.A$ over $t'$, if there exists $P_0 : T \to E.C$ with $P_0$ followed by $E.\mathrm{lev}$ equal to $P$ followed by $g$, then $P$ factors through $E'.\mathrm{lev}$, i.e. there is $P_0' : T \to E'.C$ with $P_0'$ followed by $E'.\mathrm{lev}$ equal to $P$.
--
--   The level subscheme of a fake elliptic curve is compatible with base change: over a cartesian square the level datum of the base-changed curve is exactly the preimage of the level datum upstairs, not merely contained in it. This upgrades the one-directional level clause occurring in `CerednikDrinfeld.QM.IsPullback` to an equivalence, and is used in the construction of isogenies with extra level structure and in the uniqueness statements for pullbacks of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (g : E'.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      FactorsThrough E'.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) :
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) → FactorsThrough E'.lev P := by sorry
