-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
-- name    : AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ed12f0fe-7ce4-5f99-a1f8-3f51cc553e47
-- title:
--   Pull-back of differentials scales simple residues by e
-- statement:
--   Let $K$ be a perfect field and let $F$, $F'$ be fields equipped with $K$-algebra structures. Assume $F$ is a one-variable function field over $K$ in the sense that there is $x \in F$ transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`, and likewise that there is $x' \in F'$ transcendental over $K$ with $F'$ finite-dimensional over $K(x')$. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, let $w$ be a place of $F'$ (a valuation subring of $F'$ containing the image of $K$, distinct from $F'$ itself, and a principal ideal ring), and let $\omega \in \Omega_{F/K}$. Write $v =$ `w.restrictAlong φ hφ` for the place of $F$ whose valuation subring is the preimage under $\varphi$ of that of $w$, write $\varphi^{*}\omega =$ `Differential.pullbackAlong φ ω` for the image of $\omega$ under the map $\Omega_{F/K} \to \Omega_{F'/K}$ induced by $\varphi$, and let $e =$ `w.ramificationIndexAlong φ` be the least positive natural number of the form $\mathrm{ord}_w(\varphi f)$ for some $f \in F$, $f \neq 0$. Each place $u$ carries a chosen uniformiser $\pi_u$ of its valuation subring and the differential $\mathrm{d}\pi_u \in \Omega$. The conclusion is the conjunction of three implications: first, if $\omega = f \cdot \mathrm{d}\pi_v$ for some $f$ in the valuation subring of $v$, then $\varphi^{*}\omega = g \cdot \mathrm{d}\pi_w$ for some $g$ in the valuation subring of $w$; second, if $\omega = f \cdot \mathrm{d}\pi_v$ with $\pi_v f$ in the valuation subring of $v$, then $\varphi^{*}\omega = g \cdot \mathrm{d}\pi_w$ with $\pi_w g$ in the valuation subring of $w$; third, for every $r \in K$, if $\omega = f \cdot \mathrm{d}\pi_v$ with $\pi_v f$ lying in the valuation subring of $v$ and having residue the image of $r$ in the residue field of $v$, then $\varphi^{*}\omega = g \cdot \mathrm{d}\pi_w$ for some $g$ with $\pi_w g$ in the valuation subring of $w$ and residue the image of $(e : K) \cdot r$ in the residue field of $w$. Only these implications are asserted, not their converses; note that $(e : K)$ is the image of the natural number $e$ in $K$, hence vanishes when the characteristic of $K$ divides $e$.
--
--   This is the functoriality of residues of differentials under a finite (here: integral) morphism of one-variable function fields: pulling back preserves regularity and at-most-simple poles and multiplies a simple residue by the ramification index, in the form $\mathrm{res}_w(\varphi^{*}\omega) = e(w|v)\,\mathrm{res}_v(\omega)$. It is used in the computation of residues of Hecke-translated differentials on modular curves, via [`ModularCurve.heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime`](thm.html#ModularCurve.heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [PerfectField K]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    {x' : F'} (htr' : Transcendental K x') (hfd' : FiniteDimensional ↥(IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') (ω : Ω[F⁄K]) :
    ((w.restrictAlong φ hφ).IsRegularAt ω → w.IsRegularAt (AlgebraicCurve.Differential.pullbackAlong φ ω)) ∧
    ((w.restrictAlong φ hφ).HasSimplePoleAt ω → w.HasSimplePoleAt (AlgebraicCurve.Differential.pullbackAlong φ ω)) ∧
    (∀ r : K, (w.restrictAlong φ hφ).HasSimpleResidue ω r →
      w.HasSimpleResidue (AlgebraicCurve.Differential.pullbackAlong φ ω) ((w.ramificationIndexAlong φ : K) * r)) := by sorry
