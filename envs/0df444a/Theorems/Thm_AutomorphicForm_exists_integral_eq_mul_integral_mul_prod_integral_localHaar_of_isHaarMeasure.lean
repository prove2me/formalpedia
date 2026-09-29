-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
-- name    : AutomorphicForm.exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/377d747a-a0d2-5a4e-9135-406d47ce784a
-- title:
--   Adelic Haar integral factors over the places of GL₂
-- statement:
--   Let $K$ be a number field, let $\mu$ be a Haar measure on $GL_2(\mathbb{A}_K)$ for the Borel $\sigma$-algebra `glBorel`, and let $\nu$ be a Haar measure on $GL_2(K_\infty)$, $K_\infty$ the infinite adele ring, for the Borel $\sigma$-algebra `glBorelOf`. Then there is a real $c>0$, depending only on these data, such that for every finite set $S$ of nonzero primes of $\mathcal{O}_K$, every $f\colon GL_2(\mathbb{A}_K)\to\mathbb{C}$, every $f_\infty\colon GL_2(K_\infty)\to\mathbb{C}$ and every family $f_v\colon GL_2(K_v)\to\mathbb{C}$ indexed by the primes $v$, subject to: $f_\infty$ is almost everywhere strongly measurable for $\nu$; each $f_v$ with $v\in S$ is almost everywhere strongly measurable for the Haar measure `localHaar` on $GL_2(K_v)$ normalised to give mass $1$ to the set of $g$ such that both $g$ and $g^{-1}$ have entries in $\mathcal{O}_v$; $f(g)=f_\infty(g_\infty)\prod_{v\in S}f_v(g_v)$ whenever every component $g_v$ with $v\notin S$ lies in that integral set; and $f(g)=0$ whenever some component $g_v$ with $v\notin S$ does not; one has $\int f\,d\mu = c\cdot\bigl(\int f_\infty\,d\nu\bigr)\cdot\prod_{v\in S}\int f_v\,d(\mathrm{localHaar})$, all integrals being Bochner integrals. Here $g_\infty$ and $g_v$ denote the images of $g$ under the archimedean projection and under the composite of the finite-adelic projection with evaluation at $v$.
--
--   This is the statement that Haar measure on $GL_2(\mathbb{A}_K)$ is, up to a positive scalar independent of $S$, the product of a Haar measure on $GL_2(K_\infty)$ with the restricted product of the local Haar measures normalised by $\mu_v(GL_2(\mathcal{O}_v))=1$; it is the measure-theoretic input for expressing adelic integrals of factorisable functions as products of local integrals. It is used in the construction of matching functions on adelic groups and in the orbital-integral comparisons that feed the local computations with Satake parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem AutomorphicForm.exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
    (K : Type) [Field K] [NumberField K]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μ = c * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v) := by sorry
