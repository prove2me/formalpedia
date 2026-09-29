-- Prove2me | Theorems.Thm_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_eq_mul_integral
-- name    : AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_eq_mul_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1aaa6eab-e475-5118-b142-60db817910df
-- title:
--   Haar compatibility of the local trace push-forward
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $v$ be a nonzero prime of $\mathcal{O}_K$, and write $K_v$ for the $v$-adic completion of $K$. Equip $K_v$ and the $K_v$-algebra $L \otimes_K K_v$ with Borel measurable structures, and let $\mu$ be an additive Haar measure on $K_v$ and $\nu$ an additive Haar measure on $L \otimes_K K_v$. The assertion is that there exists a real constant $c > 0$ such that for every $\Phi : L \otimes_K K_v \to \mathbb{C}$ that is locally constant and has compact support, $$\int_{K_v} \bigl(\mathrm{localTracePushforward}\ K\ L\ v\ \Phi\bigr)(r)\, d\mu(r) \;=\; c \int_{L \otimes_K K_v} \Phi(x)\, d\nu(x).$$ Here the push-forward at $r \in K_v$ is, by definition, the integral of $w \mapsto \Phi\bigl((\,[L:K]\,)^{-1} \otimes r + \sum_i c_i \otimes w_i\bigr)$ over $w \in K_v^{d}$, where $d$ is the $K$-dimension of the kernel of $\mathrm{Tr}_{L/K}$, the $c_i$ are the members of the chosen finite $K$-basis `Module.finBasis` of that kernel viewed in $L$, and the integration is against the $d$-fold product of the canonical additive Haar measure of $K_v$ rescaled by the inverse of its mass on the ring of $v$-adic integers $\mathcal{O}_v$. The constant $c$ is independent of $\Phi$.
--
--   This is the compatibility of Haar measures under the fibration of $L \otimes_K K_v$ over $K_v$ by the trace-zero hyperplane: integrating the trace push-forward of a test function against a Haar measure on $K_v$ computes, up to a positive constant, its integral on the semi-local algebra. It is used in the computation of the local zeta factors of the twisted unipotent term at unramified places, through [`TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram`](thm.html#TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_eq_mul_integral.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_eq_mul_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : L ⊗[K] v.adicCompletion K → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ →
      ∫ r, AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r ∂μ = (c : ℂ) * ∫ x, Φ x ∂ν := by sorry
