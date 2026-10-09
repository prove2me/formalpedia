-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_3_8
-- name    : ErdosRenyiLSC.Main.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:30.181072+00:00
-- url     : https://prove2.me/theorems/cea4c20e-7c87-486c-940c-e0bd96270c4d
-- title:
--   Lemma 3.8 (ii), pp. 17–18 — large deviation bounds (3.19)–(3.21) for slowly decaying moments
-- statement:
--   Fix $A_0\ge10$ and $C>0$. There is $\nu>0$, depending only on $A_0$ and $C$, with the following property. Let $a_0>0$, let $\xi=\xi_N$ satisfy $1+a_0\le\xi\le A_0\log\log N$, let $q=q_N$ satisfy $(\log N)^{3\xi}\le q\le CN^{1/2}$, and let $a_1,\dots,a_N$ be independent, centered complex random variables with
--   $$\mathbb E|a_i|^p\le\frac{C^p}{Nq^{p-2}}\qquad\text{for } 2\le p\le(\log N)^{A_0\log\log N}.$$
--   Then for $N\ge N_0$ and for all deterministic $A_i\in\mathbb C$ and $B_{ij}\in\mathbb C$, each of the following holds with probability at least $1-e^{-\nu(\log N)^\xi}$:
--   $$\Bigl|\sum_{i=1}^NA_ia_i\Bigr|\le(\log N)^\xi\Bigl[\frac{\max_i|A_i|}{q}+\Bigl(\frac1N\sum_{i=1}^N|A_i|^2\Bigr)^{1/2}\Bigr],$$
--   $$\Bigl|\sum_{i=1}^N\bar a_iB_{ii}a_i-\sum_{i=1}^N\sigma_i^2B_{ii}\Bigr|\le(\log N)^\xi\frac{B_d}{q},$$
--   $$\Bigl|\sum_{i\ne j}\bar a_iB_{ij}a_j\Bigr|\le(\log N)^{2\xi}\Bigl[\frac{B_o}{q}+\Bigl(\frac1{N^2}\sum_{i\ne j}|B_{ij}|^2\Bigr)^{1/2}\Bigr],$$
--   where $\sigma_i^2=\mathbb E|a_i|^2$, $B_d=\max_i|B_{ii}|$ and $B_o=\max_{i\ne j}|B_{ij}|$.
--
--   These large deviation bounds control the linear and quadratic forms in the rows of $H$ that appear in the Schur-complement formulas, under moment assumptions much weaker than sub-Gaussian tails.
--
--   **Formalization Note** The random variables form a sequence indexed by $N$ on one probability space, and all hypotheses hold for all sufficiently large $N$. The threshold $N_0$ does not depend on the coefficients $A_i,B_{ij}$. The moment exponent $p$ is real and integrability is explicit. The paper's standing condition (2.6) on $q$ is assumed, with the same constant $C$ as the moment bound. Part (i) is not formalized; part (iii) is not formalized because the printed (3.22) omits a diagonal variance term (see the mission notes).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, pp. 17–18, Lemma 3.8 (ii), (3.18)–(3.21)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section
open ProbabilityTheory

namespace ErdosRenyiLSC.Main

/-- Lemma 3.8 (ii), pp. 17–18: large deviation bounds (3.19)–(3.21) for centered
independent `a₁, …, a_N` with `E|a_i|^p ≤ C^p / (N q^{p-2})`, `2 ≤ p ≤ (log N)^{A₀ log log N}`,
uniformly over all deterministic coefficients `A_i, B_ij ∈ ℂ`. Here `σ_i² = E|a_i|²`,
`B_d = max_i |B_ii|`, `B_o = max_{i≠j} |B_ij|`. -/
theorem lemma_3_8 :
    ∀ (A₀ C : ℝ), 10 ≤ A₀ → 0 < C →
      ∃ ν : ℝ, 0 < ν ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (a : (N : ℕ) → Fin N → Ω → ℂ) (ξ q : ℕ → ℝ) (a₀ : ℝ),
          0 < a₀ →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            1 + a₀ ≤ ξ N ∧ ξ N ≤ A₀ * Real.log (Real.log (N : ℝ))) →
          (∀ᶠ (N : ℕ) in Filter.atTop,
            Real.log (N : ℝ) ^ (3 * ξ N) ≤ q N ∧ q N ≤ C * Real.sqrt (N : ℝ)) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ i : Fin N, Measurable (a N i)) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), iIndepFun (a N) P) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ i : Fin N,
            MeasureTheory.Integrable (a N i) P ∧ ∫ ω, a N i ω ∂P = 0) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i : Fin N) (p : ℝ),
            2 ≤ p → p ≤ Real.log (N : ℝ) ^ (A₀ * Real.log (Real.log (N : ℝ))) →
            MeasureTheory.Integrable (fun ω => ‖a N i ω‖ ^ p) P ∧
            ∫ ω, ‖a N i ω‖ ^ p ∂P ≤ C ^ p / ((N : ℝ) * q N ^ (p - 2))) →
          ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Acoef : Fin N → ℂ) (B : Matrix (Fin N) (Fin N) ℂ),
            -- (3.19)
            P {ω | ¬ (‖∑ i, Acoef i * a N i ω‖ ≤
                Real.log (N : ℝ) ^ ξ N *
                  (((Finset.univ.sup fun i => ‖Acoef i‖₊ : NNReal) : ℝ) / q N +
                    Real.sqrt ((1 / (N : ℝ)) * ∑ i, ‖Acoef i‖ ^ 2)))} ≤
              ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N)) ∧
            -- (3.20)
            P {ω | ¬ (‖∑ i, star (a N i ω) * B i i * a N i ω -
                  ∑ i, ((∫ ω', ‖a N i ω'‖ ^ 2 ∂P : ℝ) : ℂ) * B i i‖ ≤
                Real.log (N : ℝ) ^ ξ N *
                  (((Finset.univ.sup fun i => ‖B i i‖₊ : NNReal) : ℝ) / q N))} ≤
              ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N)) ∧
            -- (3.21)
            P {ω | ¬ (‖∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
                    star (a N i ω) * B i j * a N j ω‖ ≤
                Real.log (N : ℝ) ^ (2 * ξ N) *
                  ((((Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).sup
                        fun p => ‖B p.1 p.2‖₊ : NNReal) : ℝ) / q N +
                    Real.sqrt ((1 / (N : ℝ) ^ 2) *
                      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), ‖B i j‖ ^ 2)))} ≤
              ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N)) := by sorry

end ErdosRenyiLSC.Main
