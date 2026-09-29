-- Prove2me | Theorems.Thm_AvramDividend_BailOut_theorem1_double_barrier_expectations
-- name    : AvramDividend.BailOut.theorem1_double_barrier_expectations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:05:51.557657+00:00
-- url     : https://prove2.me/theorems/b48d9f99-3eee-439a-8ef0-b0dbac492a20
-- title:
--   Theorem 1 — discounted dividends and injections of the doubly reflected Lévy process
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, let $q>0$, and let $W^{(q)}$, $Z^{(q)}$, $\overline Z^{(q)}$ be its scale functions and $\psi'(0+)=E[X_1]$. Let $a>0$, $x\in[0,a]$, and let $(L^a,R^0)$ be a double-barrier strategy $\bar\pi_{0,a}$ from initial capital $x$. Then
--
--   $$\mathbf E_x\Bigl[\int_0^\infty e^{-qt}\,dL^a_t\Bigr]=\frac{Z^{(q)}(x)}{qW^{(q)}(a)},$$
--
--   $$\mathbf E_x\Bigl[\int_0^\infty e^{-qt}\,dR^0_t\Bigr]=-\overline Z^{(q)}(x)-\frac{\psi'(0+)}{q}+\frac{Z^{(q)}(a)}{qW^{(q)}(a)}Z^{(q)}(x).$$
--
--   Together with the definition of the value, this identifies the value of $\bar\pi_{0,a}$ as the candidate $\bar v_a$ of (5.4).
--
--   **Formalization Note** Both sides are compared in the extended reals, so the statement also asserts that the expectations are finite and the right-hand sides nonnegative. The paper adds that (4.4) is $+\infty$ if $\psi'(0+)=-\infty$; that case is excluded by the standing assumption $E[X_1]>-\infty$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 11, Theorem 1, eqs. (4.3)–(4.4)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BailOutProblem

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem theorem1_double_barrier_expectations {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W)
    (a x : ℝ) (ha : 0 < a) (hx : x ∈ Set.Icc 0 a) (π : Policy Ω)
    (hπ : IsDoubleBarrier Lv a x π) :
    ((∫⁻ ω, discountedIntegral q (fun t => π.L t ω) ∂P : ℝ≥0∞) : EReal) =
        ((Zq q W x / (q * W a) : ℝ) : EReal) ∧
      ((∫⁻ ω, discountedIntegral q (fun t => π.R t ω) ∂P : ℝ≥0∞) : EReal) =
        ((-Zbar q W x - Lv.psiDerivZero / q + Zq q W a / (q * W a) * Zq q W x : ℝ) : EReal) := by sorry

end AvramDividend.BailOut
