-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_corollary_4_4
-- name    : BlindProphetSec.Blind.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:50.01191+00:00
-- url     : https://prove2.me/theorems/8815820d-4bc8-4f95-9777-9e8bbcce9caf
-- title:
--   Corollary 4.4, p. 16 — some 1 ≥ α₁ ≥ … ≥ α_m ≥ 0 gives E(V_{σ_T}) ≥ 0.66975 E(maxᵢ Vᵢ) for α = α_{α₁…α_m}
-- statement:
--   There exist $m\ge1$ and $1\ge\alpha_1\ge\dots\ge\alpha_m\ge0$ such that, for $\alpha=\alpha_{\alpha_1,\dots,\alpha_m}$ the piecewise-constant blind strategy $\alpha(x)=\sum_{j\in[m]}\alpha_j\mathbf 1_{[\frac{j-1}m,\frac jm)}(x)$, every $n$ and every instance $F_1,\dots,F_n$ of continuous laws of independent nonnegative random variables arriving in uniformly random order,
--   $$\mathbb E(V_{\sigma_T})\;\ge\;0.66975\;\mathbb E\big(\max_{i\in[n]}V_i\big),$$
--   where $T$ is the stopping time of the blind strategy $\alpha$. The paper reports that $m=30$ suffices.
--
--   This is the numerical consequence of Lemma 4.3 and gives Theorem 1.1.
--
--   **Formalization Note.** The ratio is stated multiplied out in $[0,\infty]$. The coefficients $(m,\alpha_1,\dots,\alpha_m)$ are chosen once, before $n$ and the instance: one strategy guarantees the constant on every instance. The value $m=30$ is not part of the formal statement.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 16, Corollary 4.4 and the sentence after it

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem corollary_4_4 :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ a : ℕ → ℝ, a 1 ≤ 1 ∧ AntitoneOn a (Set.Icc 1 m) ∧ 0 ≤ a m ∧
      ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)],
        (∀ i, μ i (Set.Iio 0) = 0) →
        ENNReal.ofReal (66975 / 100000) * Emax μ ≤ blindValue (pieceAlpha m a) μ := by sorry

end BlindProphetSec.Blind
