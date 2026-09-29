-- Prove2me | Theorems.Thm_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6d09e7b8-050e-5c19-8674-8a160defe909
-- title:
--   Integral twisted orbits at unramified places of GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma^{n}=1$ where $n=\operatorname{finrank}_K L$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ such that every prime $w$ of $\mathcal{O}_L$ lying under which $v$ sits (i.e. with `HeightOneSpectrum.under (𝓞 K) w = v`) has ramification index `Ideal.ramificationIdx'` equal to $1$. Write $A=L\otimes_K K_v$, where $K_v$ is the $v$-adic completion, let the semi-local integers be the image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_v}$ in $A$ under `HeightOneSpectrum.tensorAdicCompletionIntegersTo`, and let the semi-local integral set in $\mathrm{GL}_2(A)$ consist of those $g$ for which both $g$ and $g^{-1}$ satisfy `integralMatrixSet` for that set of semi-local integers (the entrywise integrality condition). Let $\sigma$ act on $\mathrm{GL}_2(A)$ entrywise through $\sigma\otimes\mathrm{id}_{K_v}$, and for $\delta\in\mathrm{GL}_2(A)$ put $N\delta=\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ (`normString`, the ordered product over $i\in\{0,\dots,n-1\}$ of the $i$-th iterate). Assume $\delta$ lies in the semi-local integral set and that there is a semi-local integer $u$ with $u\,\bigl(\operatorname{tr}(N\delta)^2-4\det(N\delta)\bigr)=1$. Then every $z\in\mathrm{GL}_2(A)$ which commutes with $N\delta$ and satisfies $z^{-1}\delta\,\sigma(z)$ in the semi-local integral set lies in the product set $T'\cdot\mathrm{GL}_2(\mathcal{O})$, where $T'$ is the twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1}=\delta\}$ and $\mathrm{GL}_2(\mathcal{O})$ is the semi-local integral set.
--
--   This is the local statement used at all but finitely many places in the study of adelic twisted orbital integrals for cyclic base change of $\mathrm{GL}_2$: at a place $v$ unramified in $L$ where the component $\delta_v$ is integral and the discriminant of its norm is a unit, the integral points of the twisted orbit of $\delta_v$ are accounted for by the twisted centraliser together with the maximal compact subgroup. It feeds the compactness assertion [`AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul`](thm.html#AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

theorem AutomorphicForm.setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (hdisc : ∃ u ∈ AutomorphicForm.semiLocalIntegers K L v,
      u * (Matrix.trace ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
            4 * Matrix.det ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1) :
    {z : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        z ∈ Subgroup.centralizer
            ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} :
              Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧
          z⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z ∈
            AutomorphicForm.semiLocalIntegralSet K L v} ⊆
      (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * AutomorphicForm.semiLocalIntegralSet K L v := by sorry
