-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_proposition_11
-- name    : CPDNetworks.Unknown.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:46.971808+00:00
-- url     : https://prove2.me/theorems/895bbe88-2592-4587-ac83-deabe162408c
-- title:
--   Proposition 11, p. 50 (Bandeira–van Handel 2016) — P{‖W‖_{2→2} ≥ 2√2(1+ϵ)σ + x} ≤ m exp(−x²/(c_ϵσ_*²))
-- statement:
--   Let $W$ be a random symmetric $m\times m$ matrix ($m\ge1$) on a probability space $(\Omega,\mathcal F,\mathrm P)$ whose entries $W_{ij}$, $i\le j$, are independent, centred, and bounded in absolute value by $\sigma_*>0$ almost surely. Put
--   $$\sigma=\max_i\Big[\sum_j\operatorname{var}(W_{ij})\Big]^{1/2}.$$
--   Then for every $0<\epsilon\le1/2$ there is a constant $c_\epsilon>0$, depending only on $\epsilon$, such that for every $x\ge0$
--   $$\mathrm P\big\{\|W\|_{2\to2}\ge2\sqrt2(1+\epsilon)\sigma+x\big\}\le m\exp\Big(-\frac{x^2}{c_\epsilon\sigma_*^2}\Big).$$
--
--   This is the sharp non-asymptotic bound on the spectral norm of a random matrix with independent entries (Bandeira and van Handel, 2016, Corollary 3.12 and Remark 3.13). In the paper it is the tool behind the noise bound of Lemma 12.
--
--   **Formalization Note.** The constant $c_\epsilon$ is chosen before $m$, the probability space and the matrix, and is required to be positive; with $c_\epsilon\le0$ the right-hand side would be at least $m$ and the bound empty. "Independent entries" of a symmetric matrix means the family $(W_{ij})_{i\le j}$ is mutually independent. $m\ge1$ is added: for $m=0$ and $x=0$ the event is the whole space and the right-hand side is $0$. Entries are measurable real functions, bounded almost surely; variances are Mathlib's `variance`.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 50, Proposition 11 (citing Bandeira and van Handel 2016, Corollary 3.12 and Remark 3.13)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

open MeasureTheory ProbabilityTheory

namespace CPDNetworks.Unknown

/-- Proposition 11, p. 50 (Bandeira and van Handel 2016, Cor. 3.12 and Rem. 3.13). -/
theorem proposition_11 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ cε : ℝ, 0 < cε ∧
    ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Fin m → Fin m → Ω → ℝ) (σstar : ℝ),
      1 ≤ m →
      (∀ i j, Measurable (W i j)) →
      (∀ i j w, W i j w = W j i w) →
      iIndepFun (fun p : {p : Fin m × Fin m // p.1 ≤ p.2} => W p.1.1 p.1.2) P →
      (∀ i j, ∫ w, W i j w ∂P = 0) →
      0 < σstar →
      (∀ i j, ∀ᵐ w ∂P, |W i j w| ≤ σstar) →
      ∀ x : ℝ, 0 ≤ x →
        (P {w | 2 * Real.sqrt 2 * (1 + ε) * (⨆ i, Real.sqrt (∑ j, variance (W i j) P)) + x ≤
            matrixOpNorm (Matrix.of fun i j => W i j w)}).toReal ≤
          m * Real.exp (-x ^ 2 / (cε * σstar ^ 2)) := by sorry

end CPDNetworks.Unknown
