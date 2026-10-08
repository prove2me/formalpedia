-- Prove2me | Theorems.Thm_BERicci_Stab_lemma_5_7_ii
-- name    : BERicci.Stab.lemma_5_7_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:49.609836+00:00
-- url     : https://prove2.me/theorems/7494c1eb-dcbd-4002-a1b0-b985f951d542
-- title:
--   Lemma 5.7(ii) — weak convergence plus convergence of squared norms, or of entropies, implies graph-law convergence
-- statement:
--   Let $m_n\to m_\infty$ in $\mathcal P_2(X)$ on a complete separable metric space, and let $f_n\in L^2(X,m_n)$ and $f_\infty\in L^2(X,m_\infty)$.
--
--   1. If for every bounded continuous $\varphi:X\to\mathbb R$
--
--   $$\int_X f_n\varphi\,dm_n\longrightarrow\int_X f_\infty\varphi\,dm_\infty,\qquad
--     \int_X f_n^2\,dm_n\longrightarrow\int_X f_\infty^2\,dm_\infty,$$
--
--   then the graph laws $(\mathrm{id},f_n)_\#m_n$ converge in $W_2$ to $(\mathrm{id},f_\infty)_\#m_\infty$.
--
--   2. The same conclusion holds if the $f_n$ are uniformly bounded probability densities ($0\le f_n\le C$ $m_n$-a.e., $\int f_n\,dm_n=1$), $f_\infty$ is a probability density, $f_nm_n\rightharpoonup f_\infty m_\infty$ weakly, and
--   $$\int_X f_n\log f_n\,dm_n\longrightarrow\int_X f_\infty\log f_\infty\,dm_\infty.$$
--
--   These criteria turn weak testing together with convergence of a strictly convex integral into the stronger function convergence of Definition 5.6.
--
--   **Formalization Note** The two assertions of part (ii) are the two conjuncts. Measurable representatives are explicit; all Bochner integrals are of integrable functions (bounded or $L^2$ integrands against probability measures; $|x\log x|\le 1+x^2$ for $x\ge0$).
-- source:
--   arXiv:1209.5786v4, Lemma 5.7(ii), p. 64

import Mathlib
import Definitions.Def_BERicci_Stab_Convergence

namespace BERicci.Stab

open MeasureTheory Filter Topology

/-- Lemma 5.7(ii), p. 64: both scalar criteria. The first conjunct is the criterion by weak
convergence and convergence of `∫ f_n² dm_n`; the second is the criterion for uniformly bounded
probability densities by weak convergence of `f_n m_n` and convergence of `∫ f_n log f_n dm_n`. -/
theorem lemma_5_7_ii {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : ℕ → Measure X) (mlim : Measure X)
    (hm : ∀ n, BERicci.Gamma.InP2 (m n)) (hmlim : BERicci.Gamma.InP2 mlim)
    (hmconv : Tendsto (fun n => BERicci.Gamma.W2sq (m n) mlim) atTop (𝓝 0)) :
    (∀ (f : ℕ → X → ℝ) (flim : X → ℝ),
      (∀ n, Measurable (f n) ∧ MemLp (f n) 2 (m n)) →
      (Measurable flim ∧ MemLp flim 2 mlim) →
      (∀ φ : BoundedContinuousFunction X ℝ,
        Tendsto (fun n => ∫ x, f n x * φ x ∂m n) atTop
          (𝓝 (∫ x, flim x * φ x ∂mlim))) →
      Tendsto (fun n => ∫ x, (f n x) ^ 2 ∂m n) atTop
        (𝓝 (∫ x, (flim x) ^ 2 ∂mlim)) →
      ScalarConverges m mlim f flim) ∧
    (∀ (f : ℕ → X → ℝ) (flim : X → ℝ),
      (∀ n, Measurable (f n)) → Measurable flim → MemLp flim 2 mlim →
      (∃ C : ℝ, ∀ n, ∀ᵐ x ∂m n, 0 ≤ f n x ∧ f n x ≤ C) →
      (∀ n, ∫ x, f n x ∂m n = 1) →
      0 ≤ᵐ[mlim] flim → ∫ x, flim x ∂mlim = 1 →
      (∀ φ : BoundedContinuousFunction X ℝ,
        Tendsto (fun n => ∫ x, φ x * f n x ∂m n) atTop
          (𝓝 (∫ x, φ x * flim x ∂mlim))) →
      Tendsto (fun n => ∫ x, f n x * Real.log (f n x) ∂m n) atTop
        (𝓝 (∫ x, flim x * Real.log (flim x) ∂mlim)) →
      ScalarConverges m mlim f flim) := by sorry

end BERicci.Stab
