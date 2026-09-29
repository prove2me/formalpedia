-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
-- name    : AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d1ce1eb8-6670-59c3-b0ba-a03047016611
-- title:
--   Correspondences on divisors and logarithmic differentials agree
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be fields equipped with $K$-algebra structures, and assume $F'$ has principal divisors in the sense that every nonzero $h \in F'$ admits a finitely supported $\mathbb{Z}$-valued function on the places of $F'/K$ whose value at each place $v$ is $\operatorname{ord}_v h$ and whose degree is $0$ (places being valuation subrings of $F'$ containing the image of $K$, proper, and principal ideal rings). Let $\varphi, \psi : F \to F'$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, and assume that, for the $F$-algebra structure on $F'$ given by $\psi$, the module $F'$ is finite over $F$, that the push-forward norm formula for divisors along this extension holds, and that $F'$ is separable over $F$. Let $n \in \mathbb{Z}$, let $D$ be a divisor of $F/K$ (a finitely supported $\mathbb{Z}$-valued function on places of $F/K$) and let $f \in F$, $f \neq 0$, satisfy $n \cdot D(v) = \operatorname{ord}_v f$ for every place $v$ of $F/K$. Then there exists $g \in F$ with $g = N_{F'/F}(\varphi f)$, the field norm taken for the $F$-algebra structure induced by $\psi$, such that $g \neq 0$; such that $n \cdot (\psi_* \varphi^* D)(v) = \operatorname{ord}_v g$ for every place $v$ of $F/K$, where $\varphi^*$ is pull-back of divisors along $\varphi$ and $\psi_*$ push-forward along $\psi$; and such that, in $\Omega_{F/K}$, $$g^{-1} \, dg = \operatorname{tr}_\psi\bigl(\varphi^*(f^{-1} \, df)\bigr),$$ where $\varphi^*$ on Kähler differentials is the $K$-linear map $\Omega_{F/K} \to \Omega_{F'/K}$ induced by $\varphi$, and $\operatorname{tr}_\psi$ is the trace map $\Omega_{F'/K} \to \Omega_{F/K}$, which under the separability hypothesis is the algebra trace of $F'/F$ transported through the base-change isomorphism $F' \otimes_F \Omega_{F/K} \cong \Omega_{F'/K}$.
--
--   This is the divisor- and function-level form of the compatibility of Serre's logarithmic differential map $\operatorname{dlog} : \operatorname{Pic}^0(F/K)[n] \to \Omega_{F/K}$, sending the class of $D$ with $nD = \operatorname{div} f$ to $df/f$, with a correspondence $T = \psi_* \varphi^*$: the pair $(D,f)$ is carried to $(TD, N_\psi(\varphi f))$, and $\operatorname{dlog}$ of the image is $\operatorname{tr}_\psi \varphi^* \operatorname{dlog}$ of the original. It is used for the corresponding statement on $n$-torsion of $\operatorname{Pic}^0$ and thence for the action of Hecke operators on differentials of modular curves modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K ψ) (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hsep : AlgebraicCurve.SeparableAlong K ψ)
    (n : ℤ) (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := AlgebraicCurve.algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : AlgebraicCurve.Place K F,
        n * AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        AlgebraicCurve.Differential.traceAlong ψ
          (AlgebraicCurve.Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) := by sorry
