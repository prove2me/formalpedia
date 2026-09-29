-- Prove2me | Theorems.Thm_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat
-- name    : AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/bfc46581-63ef-511c-a0c4-bd1b530b3f6a
-- title:
--   Finite-group quotient of a flat proper π-adic tower exists
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, let $\pi \in \mathcal O$ be irreducible, and assume $\mathcal O$ is adically complete for the ideal $(\pi)$. Let $X : \mathbb N \to \mathrm{Scheme}$ be a tower of schemes, each $X_n$ equipped with a morphism $xb_n : X_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ and transition maps $xt_n : X_n \to X_{n+1}$, such that for every $n$ the square formed by $xt_n$, $xb_n$, $xb_{n+1}$ and the map $\operatorname{Spec}(\mathcal O/\pi^{n+1}) \to \operatorname{Spec}(\mathcal O/\pi^{n+2})$ induced by the quotient factorisation is a pullback; assume each $xb_n$ is proper and flat, and that in each $X_n$ every finite set of points is contained in an affine open. Let $G$ be a finite group acting on each $X_n$ by automorphisms $a_n : G \to \operatorname{Aut}(X_n)$, each automorphism being over $\operatorname{Spec}(\mathcal O/\pi^{n+1})$ (i.e. $(a_n g)\circ$ followed by $xb_n$ equals $xb_n$) and compatible with the transitions ($xt_n \circ a_n(g) = a_{n+1}(g) \circ xt_n$ in diagrammatic order). Then the type $\mathtt{TowerQuotientDatum}\ \mathcal O\ \pi\ X\ xb\ xt\ G\ a$ is nonempty: there exists a tower $Y_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ of proper flat schemes with cartesian transition squares of the same shape, together with morphisms $p_n : X_n \to Y_n$ over the base, compatible with the transitions and cartesian along them, invariant under the $G$-action, finite, surjective, epimorphic after restriction to every open of $Y_n$, and satisfying the Zariski-local universal property for $G$-invariant compatible families of morphisms out of the preimages $p_n^{-1}(U_n)$, along with the remaining conditions recorded in the structure `TowerQuotientDatum`.
--
--   This is the existence of the quotient $\mathcal X/G$ of a flat proper formal $\pi$-adic tower $\mathcal X = \varinjlim X_n$ by a finite group acting over the base, packaged levelwise as a tower quotient datum, with no tameness or freeness assumption on the action. It is used in the construction of formal quotient data in the Čerednik–Drinfeld part of the development, via [`CerednikDrinfeld.exists_formalQuotientDatum_coeff_adicFib`](thm.html#CerednikDrinfeld.exists_formalQuotientDatum_coeff_adicFib).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom) :
    Nonempty (TowerQuotientDatum 𝒪 π X xb xt G a) := by sorry
