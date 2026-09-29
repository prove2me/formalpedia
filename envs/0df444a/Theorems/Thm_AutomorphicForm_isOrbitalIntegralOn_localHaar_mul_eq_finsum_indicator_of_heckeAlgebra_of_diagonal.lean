-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
-- name    : AutomorphicForm.isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0f510488-71cf-58aa-a254-422a8d134dc1
-- title:
--   Split regular orbital integral as a coset sum
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of $\mathcal{O}_K$, and write $K_v$, $\mathcal{O}_v$ for the completion and its valuation ring and $U =$ [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) for the image of $\mathrm{GL}_2(\mathcal{O}_v)$ in $\mathrm{GL}_2(K_v)$ under the map induced by $\mathcal{O}_v \to K_v$. Let $f$ lie in the Hecke algebra of $U$ over $\mathbb{C}$, i.e. the $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(K_v) \to \mathbb{C}$ satisfying the predicate `IsHeckeFun` for $U$. Let $\alpha, \beta \in K_v^{\times}$ and $m \in \mathbb{Z}$ with $v(1 - \beta/\alpha) = \mathrm{ofAdd}(-m)$, let $\gamma \in \mathrm{GL}_2(K_v)$ have matrix $\mathrm{diag}(\alpha,\beta)$, let $\tau$ be a Haar measure for the Borel structure on the centraliser of $\{\gamma\}$, let $m_\tau \in \mathbb{R}$ satisfy $\tau$ of the preimage of $U$ in that centraliser $= \mathrm{ENNReal.ofReal}\, m_\tau$, and let $I \in \mathbb{C}$ be an orbital integral of $f$ at $\gamma$ in the sense of `IsOrbitalIntegralOn`: there is $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$, nonnegative, Borel measurable, of compact support, with $\int w(tx)\,d\tau(t) = 1$ whenever $f(x^{-1}\gamma x) \neq 0$, and $I = \int f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$ for $\mu =$ [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168), the Haar measure of $\mathrm{GL}_2(K_v)$ normalised to give mass one to `localIntegralSet K v`. The conclusion is $$m_\tau \cdot N(v)^{-m} \cdot I = \sum_{c \in \mathrm{GL}_2(K_v)/U} \mathbf{1}_S(c)\, f(\mathrm{out}(c)),$$ a finite sum over the coset space, where $N(v)$ is the absolute norm of $v$, $S$ is the set of cosets $c$ admitting a representative $g$ with $g_{10} = 0$, $g_{00} = \alpha$, $g_{11} = \beta$, and $\mathrm{out}(c)$ is a chosen representative of $c$.
--
--   This is the unfolding, via the Iwasawa decomposition, of a local orbital integral of a spherical Hecke function at a split regular semisimple element $\mathrm{diag}(\alpha,\beta)$: up to the mass $m_\tau$ of the integral points of the diagonal torus and the factor $|1-\beta/\alpha|_v = N(v)^{-m}$, it equals the constant term of $f$ along the upper unipotent subgroup at $(\alpha,\beta)$. It is used in the construction of matching local Hecke data, via [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime); the proof cites the uniqueness of orbital integrals at regular semisimple elements and the diagonal form of the Iwasawa decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem AutomorphicForm.isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (mτ : ℝ)
    (hmτ : τ (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K)))) = ENNReal.ofReal mτ)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    (mτ : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I =
      ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸
              LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c := by sorry
