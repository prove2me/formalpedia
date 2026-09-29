-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence
-- name    : AlgebraicCurve.Pic0.torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d247ce22-9256-5337-aea7-82e858617a92
-- title:
--   δ on Pic⁰[p] intertwines ψ_*φ^* with tr_ψφ^*
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, and assume $F'$ has principal divisors, i.e. every nonzero $f \in F'$ has a degree-zero divisor whose value at each place is $\operatorname{ord}_v f$. Let $\varphi, \psi : F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, and assume that $F'$ is a finite module over $F$ via $\psi$, that the pushforward norm formula holds along $\psi$, and that $F'$ is separable over $F$ via $\psi$. Let $T = \psi_* \circ \varphi^*$ be the correspondence on divisors $\operatorname{Div}(F/K) = (\mathrm{Place}(K,F) \to_{\mathrm{f}} \mathbb{Z})$, assumed to send degree-zero divisors to degree-zero divisors, and let $\bar T$ be an additive endomorphism of $\mathrm{Pic}^0(F/K)$ that computes the class of $TE$ on the class of every degree-zero divisor $E$. Fix $p \in \mathbb{N}$ and an additive map $\delta$ from the $p$-torsion of $\mathrm{Pic}^0(F/K)$ to $\Omega_{F/K}$ satisfying Serre's recipe: $\delta y = g^{-1}\,\mathrm{d}g$ whenever $E$ is a degree-zero divisor with class $y$, $g \neq 0$, and $p\,E(v) = \operatorname{ord}_v g$ for all places $v$. Then for $p$-torsion classes $x, y$ with $y = \bar T x$ one has $\delta y = \operatorname{tr}_\psi(\varphi^* (\delta x))$, where $\varphi^*$ is the map on Kähler differentials induced by $\varphi$ and $\operatorname{tr}_\psi$ is the trace map along $\psi$.
--
--   This is the compatibility, going back to Serre, between the $\mathrm{dlog}$-type map $\delta$ on $p$-torsion of the degree-zero divisor class group and a correspondence $\psi_*\varphi^*$ acting on divisor classes: the matching action on differentials is $\operatorname{tr}_\psi \circ \varphi^*$. It is used to compute the action of Hecke correspondences on differentials attached to torsion points of the Jacobian of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ)
    (hdeg : ∀ E : Divisor K F, E ∈ Divisor.degZero (K := K) (F := F) →
      Divisor.correspondence φ ψ hφ hψ E ∈ Divisor.degZero (K := K) (F := F))
    (Tbar : Pic0 K F →+ Pic0 K F)
    (hTbar : ∀ E : Divisor.degZero (K := K) (F := F),
      Tbar (Pic0.mk E) = Pic0.mk ⟨Divisor.correspondence φ ψ hφ hψ E, hdeg E E.2⟩)
    (p : ℕ) (δ : Pic0.torsion K F p →+ Ω[F⁄K])
    (hδ : ∀ (y : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (y : Pic0 K F) → g ≠ 0 →
        (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K F g)
    (x y : Pic0.torsion K F p) (hy : (y : Pic0 K F) = Tbar x) :
    δ y = Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by sorry
