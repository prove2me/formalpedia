-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/a7001411-4154-539b-9411-bd74c46c9974
-- title:
--   Smooth closed fibre from power series completions at closed points
-- statement:
--   Let $W$ be a Noetherian commutative local ring whose residue field $\mathrm{ResidueField}(W)$ is algebraically closed, and let $S$ be a commutative $W$-algebra of finite type. Assume that for every maximal ideal $\mathfrak q$ of $S$ lying over the maximal ideal $\mathfrak m_W$ of $W$ there is a ring isomorphism $e$ from the completion of the local ring $S_{\mathfrak q} = \mathrm{Localization.AtPrime}\,\mathfrak q$ with respect to its maximal ideal onto the formal power series ring $W[[X]]$, which is compatible with the structure maps in the sense that for every $a \in W$ the image in the completion of the canonical image of $a$ under $W \to S \to S_{\mathfrak q}$ is carried by $e$ to the constant series $\mathrm{C}\,a$. Then the second projection of the fibre product of $\operatorname{Spec} S \to \operatorname{Spec} W$ and $\operatorname{Spec}(\mathrm{ResidueField}(W)) \to \operatorname{Spec} W$ (the two morphisms being the ones induced by the algebra maps $W \to S$ and $W \to \mathrm{ResidueField}(W)$), that is the structure morphism of the closed fibre over $\operatorname{Spec}(\mathrm{ResidueField}(W))$, is smooth of relative dimension $1$.
--
--   This is the step passing from a power series local form at the closed points of $\operatorname{Spec} S$ to smoothness of relative dimension $1$ of the closed fibre over the residue field; it is the geometric form of the standard criterion for smoothness in terms of completed local rings at closed points of a fibre over an algebraically closed field. It feeds the deduction of relative smoothness for $\operatorname{Spec}$ of an algebra over a complete local base with algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAlgClosed (ResidueField W)]
    {S : Type} [CommRing S] [Algebra W S] [Algebra.FiniteType W S]
    (hloc : ∀ (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)],
      ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
        ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
            (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a) :
    SmoothOfRelativeDimension 1
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap W S)))
        (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W))))) := by sorry
