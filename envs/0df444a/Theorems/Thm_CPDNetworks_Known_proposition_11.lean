-- Prove2me | Theorems.Thm_CPDNetworks_Known_proposition_11
-- name    : CPDNetworks.Known.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:46.723583+00:00
-- url     : https://prove2.me/theorems/36fffc38-4579-49bd-ac36-14d8c63b26e0
-- title:
--   Proposition 11 — Bandeira–van Handel tail bound $\mathbb P\{\|W\|\ge2\sqrt2(1+\epsilon)\sigma+x\}\le m e^{-x^2/(c_\epsilon\sigma_*^2)}$
-- statement:
--   This is the concentration inequality of Bandeira and van Handel (2016, Corollary 3.12 and Remark 3.13) for symmetric random matrices with independent bounded entries.
--
--   For every $0<\epsilon\le1/2$ there is a constant $c_\epsilon>0$ with the following property. Let $m\ge1$ and let $W$ be an $m\times m$ symmetric random matrix on a probability space $(\Omega,\mathcal F,\mathbb P)$ whose entries $W_{ij}$, $i\le j$, are independent, measurable, centred, and bounded in absolute value by some $\sigma_*>0$ almost surely. Put
--   $$\sigma=\max_i\Big[\sum_j\operatorname{var}(W_{ij})\Big]^{1/2}.$$
--   Then for every $x\ge0$,
--   $$\mathbb P\big\{\|W\|_{2\to2}\ge2\sqrt2(1+\epsilon)\sigma+x\big\}\le m\exp\Big(-\frac{x^2}{c_\epsilon\sigma_*^2}\Big).$$
--
--   The constant $c_\epsilon$ depends only on $\epsilon$. This inequality is the source of the leading term $2\sqrt2(1+\epsilon)\sqrt{\omega_n}$ in the threshold of the test.
--
--   **Formalization Note.** "Independent entries" of a symmetric matrix is read as mutual independence of the entries on and above the diagonal. The size $m\ge1$ is implicit on the page and is needed: for $m=0$ and $x=0$ the event is sure while the right-hand side is $0$. The constant $c_\epsilon$ is chosen before $m$, the probability space and the matrix.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 50, Proposition 11 (Bandeira and van Handel 2016, Corollary 3.12, Remark 3.13)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

open MeasureTheory ProbabilityTheory

namespace CPDNetworks.Known

/-- Proposition 11, p. 50 (Bandeira and van Handel 2016, Corollary 3.12 and Remark 3.13). -/
theorem proposition_11 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ cε : ℝ, 0 < cε ∧
      ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : Fin m → Fin m → Ω → ℝ) (σstar x : ℝ),
        1 ≤ m →
        (∀ i j, Measurable (W i j)) →
        (∀ i j ω, W i j ω = W j i ω) →
        iIndepFun (fun p : {p : Fin m × Fin m // p.1 ≤ p.2} => W p.1.1 p.1.2) P →
        (∀ i j, ∫ ω, W i j ω ∂P = 0) →
        0 < σstar →
        (∀ i j, ∀ᵐ ω ∂P, |W i j ω| ≤ σstar) →
        0 ≤ x →
        (P {ω | 2 * Real.sqrt 2 * (1 + ε) * (⨆ i, Real.sqrt (∑ j, variance (W i j) P)) + x ≤
            matrixOpNorm (Matrix.of fun i j => W i j ω)}).toReal ≤
          m * Real.exp (-x ^ 2 / (cε * σstar ^ 2)) := by sorry

end CPDNetworks.Known
