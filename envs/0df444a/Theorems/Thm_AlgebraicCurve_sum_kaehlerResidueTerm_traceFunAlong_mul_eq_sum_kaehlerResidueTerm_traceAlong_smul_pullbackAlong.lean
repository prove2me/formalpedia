-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
-- name    : AlgebraicCurve.sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/839e0a5c-5c35-5403-a74e-5ea004a9277a
-- title:
--   Residue-pairing adjunction for a correspondence on a stable place set
-- statement:
--   Let $K$ be a field and let $F$, $R$ be fields with $K$-algebra structures, such that every nonzero element of $R$ has a degree-zero principal divisor, such that each place of $F$ and of $R$ carries its chosen canonical local residue datum, such that at each place $v$ the differential $d t_v$ of a uniformiser spans the module of Kähler differentials over the respective field, and with $\Omega_{F/K}$ and $\Omega_{R/K}$ nontrivial. Let $\alpha,\beta\colon F\to R$ be $K$-algebra maps that are integral as ring homomorphisms, each satisfying the fibre residue identity: for every place $v$, every $\omega\in\Omega_{F/K}$ and every $f'\in R$, the sum over the places of $R$ restricting to $v$ of the residue terms of the pullback of $\omega$ against the constant family $f'$ equals the residue term of $\omega$ against the constant family $\mathrm{Tr}(f')$ at $v$. Assume $R$ is separable over $F$ via $\beta$, and that every $\eta\in\Omega_{R/K}$ has the form $c\cdot\beta^{*}\omega_1$ with $c\in R$, $\omega_1\in\Omega_{F/K}$. Let $S$ be a finite set of places of $F$ stable in the sense that a place of $R$ restricts into $S$ along $\alpha$ if and only if it does along $\beta$. Then for all $g\in F$, $u\in R$ and $\omega\in\Omega_{F/K}$,
--   $$\sum_{x\in S}\mathrm{res}\text{-}\mathrm{term}_x\bigl(\omega,\ \mathrm{Tr}_\alpha(\beta(g)u)\bigr)=\sum_{z\in S}\mathrm{res}\text{-}\mathrm{term}_z\bigl(\mathrm{Tr}_\beta(u\cdot\alpha^{*}\omega),\ g\bigr),$$
--   where each residue term at a place $v$ is the trace to $K$ of the residue field value of the local residue of (constant function value) times the coefficient of the differential with respect to $d t_v$.
--
--   This is the adjunction, for the residue pairing summed over a place set stable under a correspondence, between the operator $g\mapsto\mathrm{Tr}_\alpha(\beta(g)u)$ on functions and the transposed operator $\omega\mapsto\mathrm{Tr}_\beta(u\cdot\alpha^{*}\omega)$ on differentials. It is used in the treatment of Hecke correspondences on modular curves, where it feeds the comparison of residue sums with divisorial corrections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open KaehlerDifferential AlgebraicCurve

theorem AlgebraicCurve.sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
    {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
    [HasPrincipalDivisors K R] [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K R]
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K R, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[R⁄K]]
    (α β : F →ₐ[K] R) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFα : FibreResidueIdentityAlong α hα) (hFβ : FibreResidueIdentityAlong β hβ) (hsep : SeparableAlong K β)
    (hΩ : ∀ η : Ω[R⁄K], ∃ (ω₁ : Ω[F⁄K]) (c : R), η = c • Differential.pullbackAlong β ω₁)
    (S : Finset (Place K F))
    (hS : ∀ w : Place K R, Place.restrictAlong α hα w ∈ S ↔ Place.restrictAlong β hβ w ∈ S)
    (g : F) (u : R) (ω : Ω[F⁄K]) :
    ∑ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ z ∈ S, kaehlerResidueTerm (Differential.traceAlong β (u • Differential.pullbackAlong α ω)) (diagonalHom K F g) z := by sorry
