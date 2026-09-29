-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
-- name    : AutomorphicForm.exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8b3c0664-cf60-5bf4-9d61-217596f11603
-- title:
--   Haar measure on GL₂(A_L^f) factors through semi-local components
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\mu_f$ be a measure on $\mathrm{GL}_2$ of the finite adele ring of $L$, taken with the Borel $\sigma$-algebra `glBorelOf` of that topological group, and assume $\mu_f$ is a Haar measure; let $S$ be a finite set of height-one primes of $\mathcal{O}_K$. For a height-one prime $v$ of $\mathcal{O}_K$ write $\mathrm{GL}_2(L \otimes_K K_v)$ for the general linear group over the base change of $L$ along the $v$-adic completion, let `semiLocalComponent K L v` be the group homomorphism from $\mathrm{GL}_2$ of the finite adeles of $L$ to $\mathrm{GL}_2(L \otimes_K K_v)$ obtained by applying entrywise the ring map `semiLocalEval K L v`, i.e. the product of the $w$-adic component maps over the extensions $w$ of $v$ to $L$ followed by the inverse of the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, let `semiLocalIntegralSet K L v` be the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that the entries of both $g$ and $g^{-1}$ lie in the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`, and let `semiLocalHaar K L v` be the Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised to give that set (a compact set with nonempty interior) mass $1$. The assertion is that there exists a real $c > 0$ such that for every family $F$ assigning to each height-one prime $v$ of $\mathcal{O}_K$ a complex-valued function on $\mathrm{GL}_2(L \otimes_K K_v)$, with $F_v$ continuous and compactly supported for each $v \in S$, the integral of $h \mapsto \prod_{v \in S} F_v(\mathrm{semiLocalComponent}\ K\ L\ v\ h)$ over the set of those $h$ whose component lies in `semiLocalIntegralSet K L v` for every $v \notin S$, with respect to $\mu_f$, equals $c \cdot \prod_{v \in S} \int F_v \, d(\mathrm{semiLocalHaar}\ K\ L\ v)$. The constant $c$ depends on $K$, $L$, $\mu_f$ and $S$ only, not on $F$.
--
--   This is the factorisation of an adelic Haar measure on $\mathrm{GL}_2$ into semi-local Haar measures, restricted to the open subgroup of matrices integral outside $S$: up to one global normalising constant, integration against $\mu_f$ over that subgroup is integration against the product of the normalised semi-local measures at the places of $S$. It is used in the construction of semi-local factorisations of adelic orbital integrals, via [`AutomorphicForm.exists_isSemiLocalFactorization_integral_mul_comp_inv_mul`](thm.html#AutomorphicForm.exists_isSemiLocalFactorization_integral_mul_comp_inv_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μf : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (glBorelOf (FiniteAdeleRing (𝓞 L) L)))
    (hμf : @Measure.IsHaarMeasure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) _ _
      (glBorelOf (FiniteAdeleRing (𝓞 L) L)) μf)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ F : (v : HeightOneSpectrum (𝓞 K)) → (GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ v ∈ S, Continuous (F v) ∧ HasCompactSupport (F v)) →
        ∫ h in {h | ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v},
            ∏ v ∈ S, F v (semiLocalComponent K L v h) ∂μf =
          (c : ℂ) * ∏ v ∈ S, ∫ t, F v t ∂(semiLocalHaar K L v) := by sorry
