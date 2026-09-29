-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
-- name    : CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/851a56c4-666d-5df0-880a-8ba84105ceab
-- title:
--   Functoriality of formal completion along the unit section
-- statement:
--   Let $B$ be a commutative ring, let $A$, $A'$, $A''$ be schemes (in the zeroth universe) with structure morphisms $f : A \to \operatorname{Spec} B$, $f' : A' \to \operatorname{Spec} B$, $f'' : A'' \to \operatorname{Spec} B$, let $g, g', g''$ be natural numbers, and let $\theta, \theta', \theta''$ be formal coordinate systems of the respective ranks, i.e. rules assigning to each $B$-algebra $B'$ and each tuple in $(\mathrm{Fin}\,g \to B')$ (resp. $g'$, $g''$) a morphism $\operatorname{Spec} B' \to A$ over $\operatorname{Spec} B$, and similarly for $A'$, $A''$. Here a tuple $\varphi$ of power series in $g$ variables over $B$, indexed by $\mathrm{Fin}\,g'$, is said to complete a morphism $h : A \to A'$ with $h \circ f' = f$ (in diagrammatic order $h \gg f' = f$) when for every $B$-algebra $B'$, every ideal $J \subseteq B'$ and every $n$ with $J^{n+1} = 0$, and every $s : \mathrm{Fin}\,g \to B'$ with all $s_i \in J$, one has $\theta'\bigl(B'\bigr)$ applied to the tuple of truncated evaluations $\mathrm{nilEval}\,n\,(\varphi_i)\,s$ (evaluation of the truncation of $\varphi_i$ in degrees $\le n$ in each variable) equal to the point $\theta(B')(s)$ post-composed with $h$. The theorem asserts the conjunction of: (i) the tuple $(X_i)_{i}$ of coordinate variables completes the identity of $A$ with respect to $\theta$ and $\theta$; and (ii) for all $h : A \to A'$ with $h \gg f' = f$, $h' : A' \to A''$ with $h' \gg f'' = f'$, a proof that $(h \gg h') \gg f'' = f$, and all tuples $\varphi$ (in $\mathrm{Fin}\,g' \to \mathrm{MvPowerSeries}(\mathrm{Fin}\,g, B)$) with all constant coefficients zero and $\varphi'$ (in $\mathrm{Fin}\,g'' \to \mathrm{MvPowerSeries}(\mathrm{Fin}\,g', B)$), if $\varphi$ completes $h$ with respect to $\theta, \theta'$ and $\varphi'$ completes $h'$ with respect to $\theta', \theta''$, then the substituted tuple $\bigl(\varphi'_i(\varphi_1,\dots,\varphi_{g'})\bigr)_i$ completes $h \gg h'$ with respect to $\theta, \theta''$.
--
--   This is the functoriality of passing to the formal completion at the unit section, expressed entirely in functor-of-points terms with coordinates in nilpotent ideals rather than through completed local rings. It supplies the identity and composition laws used in the rigidification arguments for fake elliptic curves, where formal completions of morphisms are transported along isomorphisms and correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp
    {B : Type} [CommRing B] {A A' A'' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {f'' : A'' ⟶ Spec (CommRingCat.of B)}
    {g g' g'' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (θ'' : RelativeGroupLaw.FormalCoordinates f'' g'') :
    IsFormalCompletionAlong θ θ (𝟙 A) (Category.id_comp f) (fun i => MvPowerSeries.X i) ∧
    ∀ (h : A ⟶ A') (hh : h ≫ f' = f) (h' : A' ⟶ A'') (hh' : h' ≫ f'' = f') (hhh' : (h ≫ h') ≫ f'' = f)
      (φ : Fin g' → MvPowerSeries (Fin g) B) (φ' : Fin g'' → MvPowerSeries (Fin g') B),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      IsFormalCompletionAlong θ θ' h hh φ → IsFormalCompletionAlong θ' θ'' h' hh' φ' →
      IsFormalCompletionAlong θ θ'' (h ≫ h') hhh' (fun i => MvPowerSeries.subst φ (φ' i)) := by sorry
