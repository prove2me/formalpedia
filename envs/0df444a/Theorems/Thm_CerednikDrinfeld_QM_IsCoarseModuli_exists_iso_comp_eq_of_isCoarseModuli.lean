-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_iso_comp_eq_of_isCoarseModuli
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/09f9ea0e-b203-540f-966d-18f35f93c443
-- title:
--   Uniqueness of coarse moduli schemes for fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a commutative ring $B$. Consider two data sets $(X,\pi_X,\mathrm{pt})$ and $(X',\pi_{X'},\mathrm{pt}')$, where $X$ and $X'$ are schemes with structure morphisms to $\operatorname{Spec} B$, and where $\mathrm{pt}$ assigns to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every fake elliptic curve $E$ over $S$ with $\Lambda$-action and level $N$ (an abelian scheme $A \to \operatorname{Spec} S$, smooth, proper, with connected two-dimensional fibres, carrying a commutative relative group law, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and satisfying the prescribed trace identity, together with level data) a morphism $\operatorname{Spec} S \to X$ whose composite with $\pi_X$ is $s$; likewise $\mathrm{pt}'$ for $X'$. Assume both are coarse moduli data: each point rule is invariant under isomorphism of fake elliptic curves, is compatible with base change along ring homomorphisms over $B$ for pullbacks of fake elliptic curves, is surjective on points over algebraically closed fields and injective there up to isomorphism, and enjoys the universal property that any point rule on another scheme over $B$ with the first two properties factors through a unique morphism from $X$ (resp. $X'$) over $B$. The conclusion is that there exists an isomorphism $i : X \cong X'$ with $\pi_{X'} \circ i = \pi_X$ and $(\mathrm{pt}'\,S\,s\,E) = i \circ (\mathrm{pt}\,S\,s\,E)$ for all $S$, $s$ and $E$. Existence only is asserted; the isomorphism is not claimed unique here.
--
--   This is the standard uniqueness statement for a coarse moduli space: two coarse moduli schemes for the same moduli problem, here fake elliptic curves with quaternionic action by $\Lambda$ and level $N$ over a base ring $B$, are identified by a unique isomorphism respecting the structure morphisms and the point rules. It is used to transfer properties such as smoothness and geometric connectedness between different constructions of the quaternionic coarse moduli scheme, and in the comparison with the Čerednik–Drinfeld uniformisation at fine level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_iso_comp_eq_of_isCoarseModuli
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX')
    (hX' : IsCoarseModuli Λ N X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by sorry
