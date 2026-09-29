-- Prove2me | Theorems.Thm_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
-- name    : Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/51a195fb-19d8-5554-923b-5de2de5b96aa
-- title:
--   Standard étale chart for a smooth complex curve at an étale coordinate
-- statement:
--   Let $S$ be a commutative ring which is an integral domain and a $\mathbb{C}$-algebra of finite type, and assume $S$ is smooth over $\mathbb{C}$ (in Mathlib's sense: formally smooth and of finite presentation over $\mathbb{C}$) and that the module of Kähler differentials $\Omega_{S/\mathbb{C}}$ has rank $1$ as an $S$-module, the rank being taken as a cardinal. Let $\sigma_0 : S \to \mathbb{C}$ be a $\mathbb{C}$-algebra homomorphism, and let $t \in S$ be such that the universal derivation $\mathrm{d}t \in \Omega_{S/\mathbb{C}}$ does not lie in the submodule $\mathfrak{m}\,\Omega_{S/\mathbb{C}}$, where $\mathfrak{m} = \ker \sigma_0$ is the maximal ideal of the point $\sigma_0$ and the submodule is the ideal $\mathfrak{m}$ acting on all of $\Omega_{S/\mathbb{C}}$. The conclusion asserts the existence of an element $g \in S$ with $\sigma_0(g) \neq 0$ such that the localization $S_g$ away from $g$, viewed as a $\mathbb{C}[X]$-algebra via the ring homomorphism $\mathbb{C}[X] \to S \to S_g$ obtained by evaluating polynomials at $t$ and then localizing, satisfies `Algebra.IsStandardEtale`: $S_g$ is standard étale over $\mathbb{C}[X]$, i.e. it is a localization of $\mathbb{C}[X][Y]/(F)$ at one element with $F$ monic in $Y$ and $\partial F/\partial Y$ invertible there.
--
--   This is the local structure theorem for étale algebras, specialised to a smooth affine curve over $\mathbb{C}$: an element $t$ whose differential generates the cotangent line at a $\mathbb{C}$-point is an étale coordinate, and after inverting a single function not vanishing at that point the curve becomes standard étale over the affine line. It is used to produce a local analytic parametrisation of such a curve near a $\mathbb{C}$-point, in [`Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential`](thm.html#Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology Polynomial

theorem Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (g : S), σ₀ g ≠ 0 ∧
      letI : Algebra (Polynomial ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (Polynomial ℂ) (Localization.Away g) := by sorry
