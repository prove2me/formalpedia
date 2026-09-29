-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
-- name    : CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/85d14fc4-410a-5bd7-a82a-3102bf615a4a
-- title:
--   Additivity of formal completion along the coordinates
-- statement:
--   Let $B$ be a commutative ring, let $A$ and $A'$ be schemes with structure morphisms $f : A \to \operatorname{Spec} B$ and $f' : A' \to \operatorname{Spec} B$, and let $g, g'$ be natural numbers. Let $\theta$ (resp. $\theta'$) assign, to each $B$-algebra $B'$ and each tuple in $(B')^{g}$ (resp. $(B')^{g'}$), a point of $A$ (resp. of $A'$) over $\operatorname{Spec} B' \to \operatorname{Spec} B$. Let $L'$ be a relative group law on $f'$ over $B$, let $F'$ be a $g'$-dimensional formal group law over $B$, and assume $\theta'$ is a system of formal coordinates for $L'$ with group law $F'$: it is natural in $B$-algebra maps on nilpotent tuples, and for every $B$-algebra $B'$ and ideal $J$ with $J^{n+1} = 0$ it maps the tuples with entries in $J$ bijectively onto the points of $A'$ that are $J$-infinitesimal for $L'$, transporting the truncated evaluation $F'.\mathrm{nilMul}\,n$ to the multiplication of $L'$. Let $h_1, h_2, h_3 : A \to A'$ be morphisms over $\operatorname{Spec} B$ (that is, $h_i$ followed by $f'$ equals $f$), and assume that for every $B$-algebra $B'$ and every point $P$ of $A$ over $\operatorname{Spec} B'$ one has $P \cdot h_3 = L'.\mathrm{mul}(P \cdot h_1, P \cdot h_2)$. Let $\varphi_1, \varphi_2 : \mathrm{Fin}\,g' \to B[[X_1,\dots,X_g]]$ have zero constant terms and complete $h_1$, $h_2$ along $\theta, \theta'$, meaning: for every $B$-algebra $B'$, ideal $J$ with $J^{n+1} = 0$ and tuple $s$ with entries in $J$, $\theta'$ applied to the truncated evaluations of the $\varphi_k$ at $s$ is the point $\theta(s)$ composed with $h_k$. Then the tuple $i \mapsto F'_i(\varphi_1, \varphi_2)$, obtained by substituting $\varphi_1, \varphi_2$ into the components of $F'$, completes $h_3$ along $\theta, \theta'$ in the same sense.
--
--   This is the additivity half of the statement that passing to formal completions at the coordinates $\theta, \theta'$ turns the pointwise group law on morphisms $A \to A'$ into the formal addition $+_{F'}$; no group law on $A$ itself is required. It is used in the study of the $\Lambda$-action on a fake elliptic curve, in particular for producing a formal module structure and the associated matrix representation of the action on formal coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates
    {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (L' : RelativeGroupLaw B f') (F' : MvFormalGroup g' B) (hθ' : L'.IsFormalCoordinates F' θ')
    (h₁ h₂ h₃ : A ⟶ A') (hh₁ : h₁ ≫ f' = f) (hh₂ : h₂ ≫ f' = f) (hh₃ : h₃ ≫ f' = f)
    (hmul : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      mapPt h₃ hh₃ P = L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h₁ hh₁ P) (mapPt h₂ hh₂ P))
    (φ₁ φ₂ : Fin g' → MvPowerSeries (Fin g) B)
    (hφ₁ : ∀ i, MvPowerSeries.constantCoeff (φ₁ i) = 0) (hφ₂ : ∀ i, MvPowerSeries.constantCoeff (φ₂ i) = 0)
    (H₁ : IsFormalCompletionAlong θ θ' h₁ hh₁ φ₁) (H₂ : IsFormalCompletionAlong θ θ' h₂ hh₂ φ₂) :
    IsFormalCompletionAlong θ θ' h₃ hh₃
      (fun i => MvPowerSeries.subst (Sum.elim φ₁ φ₂) (F'.toPowerSeries i)) := by sorry
