-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
-- name    : AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/5e0d733f-20b3-5b3b-b6ec-284496eb644b
-- title:
--   Iwasawa integration over torus shells on GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a maximal ideal of $\mathcal{O}_K$, and $\varpi$ an element of the valuation ring $\mathcal{O}_v$ of the completion $K_v$ whose image in $K_v$ is non-zero and has valuation $\exp(-1)$, i.e. a uniformiser. Equip $\mathrm{GL}_2(K_v)$ with its Borel $\sigma$-algebra (via `localGLBorel` and the associated `BorelSpace` instance). Write $N$ for the range of `unipotentGL2Hom`, the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $K_0$ for [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the place-$v$ embedding `localEmbed` of the adelic subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) at level the unit ideal, i.e. of those matrices over the finite adele ring which together with their inverses satisfy the predicate `IsLevelOneMatrix` at level $\top$. Then for every Haar measure $\mu$ on $\mathrm{GL}_2(K_v)$, every Haar measure $\mu_N$ on $N$, and every measurable $f \colon \mathrm{GL}_2(K_v) \to [0,\infty]$ satisfying $f(xg)=f(g)$ for all $x \in N$ and all $g$, setting $a_{d,n} = \mathrm{diag}(\varpi,\varpi)^{n}\,\mathrm{diag}(\varpi^{d},1)$ for $(d,n) \in \mathbb{Z}\times\mathbb{Z}$ (the `scalarPi` and `diagZ` elements), two assertions hold: first, each slice $S_{d,n} = \{x \in N : a_{d,n}^{-1} x a_{d,n} \in K_0\}$ has $\mu_N(S_{d,n})$ neither $0$ nor $\infty$; second, $$\int^{-} f(g)\,D(g)\,d\mu(g) = \sum_{(d,n)} \mu_N(S_{d,n})^{-1} \int^{-}_{K_0} f(a_{d,n}k)\,d\mu(k),$$ where $D =$ [`HaarQuotient.density`](def/HaarQuotient.html#L25) $N\,\mu_N$ is the quotient density, namely the fixed exhaustion-built weight function divided by its $\mu_N$-integral over the coset through the point.
--
--   This is the Tonelli (non-negative, possibly infinite) form of the Iwasawa integration formula for $N \backslash \mathrm{GL}_2(K_v)$ at a finite place, decomposing a density-weighted integral of a left-$N$-invariant function into integrals over the maximal compact subgroup along the torus shells $a_{d,n}$. It underlies the summation-form statement [`AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2`](thm.html#AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2) and the integrability statements for the local Rankin–Selberg integrands used in the Langlands–Tunnell part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal

theorem AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN.IsHaarMeasure]
      (f : GL (Fin 2) (v.adicCompletion K) → ℝ≥0∞), Measurable f →
      (∀ x ∈ (unipotentGL2Hom (R := v.adicCompletion K)).range, ∀ g : GL (Fin 2) (v.adicCompletion K),
        f (x * g) = f g) →
      (∀ dn : ℤ × ℤ,
        μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤} ≠ 0 ∧
        μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤} ≠ ∞) ∧
      ∫⁻ g, f g * HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN g ∂μ =
        ∑' dn : ℤ × ℤ,
          (μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
                (x : GL (Fin 2) (v.adicCompletion K)) *
                (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
              AdelicDock.localLevelOne (𝓞 K) K v ⊤})⁻¹ *
            ∫⁻ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
                Set (GL (Fin 2) (v.adicCompletion K))),
              f (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ := by sorry
