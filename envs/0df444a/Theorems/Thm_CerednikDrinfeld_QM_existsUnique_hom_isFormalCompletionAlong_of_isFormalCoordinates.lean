-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
-- name    : CerednikDrinfeld.QM.existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/9bd613fe-b454-5799-8b42-39c14d1c18d6
-- title:
--   Unique formal completion of a homomorphism along unit sections
-- statement:
--   Let $B$ be a commutative ring, let $f : A \to \operatorname{Spec} B$ and $f' : A' \to \operatorname{Spec} B$ be schemes over $B$, and let $g, g' \in \mathbb{N}$. Let $L$, $L'$ be relative group laws for $f$, $f'$, i.e. functorial group structures (multiplication, unit, inverse, with associativity, unit and inverse laws and naturality in the base scheme) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over $B$-schemes $t : T \to \operatorname{Spec} B$. Let $F$, $F'$ be formal group laws over $B$ of dimensions $g$, $g'$, and let $\theta$, $\theta'$ be families assigning to each $B$-algebra $B'$ and each tuple in $(\mathrm{Fin}\,g \to B')$, resp. $(\mathrm{Fin}\,g' \to B')$, a point of $A$, resp. $A'$, over $\operatorname{Spec} B' \to \operatorname{Spec} B$. Assume $\theta$ are formal coordinates for $L$ and $F$, and $\theta'$ for $L'$ and $F'$: each is natural along $B$-algebra maps applied to tuples of nilpotent elements, and for every $B$-algebra $B'$ and every ideal $J$ with $J^{n+1} = 0$ the map $s \mapsto \theta(s)$ sends tuples with entries in $J$ to points that reduce modulo $J$ to the unit section, is injective on such tuples, is onto the points reducing to the unit modulo $J$, and carries the truncated group law $F$ evaluated at $(s,t)$ to the product $L(\theta(s), \theta(t))$. Finally let $h : A \to A'$ satisfy $h$ followed by $f'$ equals $f$, and assume that for every $B$-algebra $B'$ composition with $h$ takes $L$-products of $B'$-points of $A$ to $L'$-products of their images. Then there is a unique homomorphism $\varphi : F \to F'$ of formal group laws (a $g'$-tuple of power series in $g$ variables with zero constant terms satisfying $\varphi \circ F = F'(\varphi, \varphi)$ under substitution) such that for every $B$-algebra $B'$, every ideal $J$ with $J^{n+1} = 0$ and every tuple $s$ with entries in $J$, one has $\theta'\bigl(i \mapsto \mathrm{nilEval}\ n\ \varphi_i\ s\bigr) = h \circ \theta(s)$, where $\mathrm{nilEval}$ evaluates at $s$ the truncation of $\varphi_i$ in degrees at most $n$ in each variable.
--
--   This is the functor-of-points form of the statement that a homomorphism of group schemes, completed along the unit sections in chosen formal coordinates, is a homomorphism of the corresponding formal group laws, and is uniquely determined by that property. It is used in the Čerednik–Drinfel'd part of the development, for the formal module structure on fake elliptic curves and for transporting group laws through lifts of relative group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
    {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f')
    (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (h : A ⟶ A') (hh : h ≫ f' = f)
    (hmul : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P Q : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      mapPt h hh (L.mul (Scheme.specOver (𝒪 := B) B') P Q) =
        L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h hh P) (mapPt h hh Q)) :
    ∃! φ : MvFormalGroup.Hom F F', IsFormalCompletionAlong θ θ' h hh φ.toPowerSeries := by sorry
