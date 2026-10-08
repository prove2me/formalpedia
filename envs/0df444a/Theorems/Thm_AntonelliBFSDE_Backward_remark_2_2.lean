-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_remark_2_2
-- name    : AntonelliBFSDE.Backward.remark_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:47.988932+00:00
-- url     : https://prove2.me/theorems/decb4331-05de-4154-885e-4f0930308906
-- title:
--   Remark 2.2 — (2.6), the optional projection identity $E(H\int a\,dC)=E(\int H_s a(s)\,dC_s)$
-- statement:
--   Let the filtered probability space satisfy the usual hypotheses. Let $a\ge0$ be a Borel function on $\mathbb R_+$. Let $C$ be an adapted process with nondecreasing càdlàg paths and $C_0\ge0$, and let $dC$ be its Stieltjes measure on $[0,\infty)$, with $C_{0-}=0$. For a random variable $H$ let $(H_t)_{t\ge0}$ be a càdlàg version of $E(H\mid\mathcal F_t)$. Then
--   $$E\Big(H\int_{[0,\infty)}a(s)\,dC_s\Big)=E\Big(\int_{[0,\infty)}H_s\,a(s)\,dC_s\Big)$$
--   in each of the two cases of the remark:
--
--   1. $H\ge0$ measurable (not necessarily integrable): $H_t$ takes values in $[0,\infty]$, is $\mathcal F_t$-measurable and satisfies $\int_B H_t\,dP=\int_B H\,dP$ for every $B\in\mathcal F_t$ (the extended conditional expectation), and the identity holds in $[0,\infty]$;
--   2. $H\in L^1(P)$ with $E\big(|H|\int_{[0,\infty)}a(s)\,dC_s\big)<\infty$: $H_t$ is real valued with $H_t=E(H\mid\mathcal F_t)$ a.s. for every $t$, and the identity holds between real numbers.
--
--   This is the form of the optional projection theorem (Lemma 2.1, after Dellacherie and Meyer, Theorem VI.57) that the proofs of Lemma 2.3 and Theorem 2.4 use, with $C=|A|$.
--
--   **Formalization Note** The paper says "$H$ is a positive or $L^1$ random variable". For positive $H$ that need not be integrable, Mathlib's `condExp` is $0$, so the positive case is stated with an $[0,\infty]$-valued càdlàg version characterised by its defining set-integral identity. The $L^1$ case is stated under the finiteness of $E(|H|\int a\,dC)$, which is what makes both sides of (2.6) defined. "Increasing process" is read as in Dellacherie–Meyer: nondecreasing right-continuous paths with $C_0\ge0$ and $C_{0-}=0$, so the integral over $[0,\infty)$ includes the atom $C_0$ at $0$. "Positive" for $a$ and $H$ means $\ge0$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 779–780, Remark 2.2, (2.6)

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Remark 2.2, (2.6) (Antonelli 1993, pp. 779–780): for a nonnegative Borel `a` on `ℝ₊` and an
adapted, nondecreasing, càdlàg `C` with `C_0 ≥ 0` (and `C_{0-} = 0`, so `dC` has an atom `C_0`
at `0`), `E(H ∫_{[0,∞)} a(s) dC_s) = E(∫_{[0,∞)} H_s a(s) dC_s)`, where `H_t` is a càdlàg version
of `E(H | 𝓕_t)`, in the two cases of the remark:
* `H` positive (measurable, `≥ 0`, not necessarily integrable): `H_t` is `[0, ∞]`-valued, an
  `𝓕_t`-measurable version of the extended conditional expectation (`∫_B H_t dP = ∫_B H dP` for
  every `B ∈ 𝓕_t`), and the identity holds in `[0, ∞]`;
* `H ∈ L¹(P)`: `H_t` is real valued with `H_t = E(H | 𝓕_t)` a.s., and the identity holds whenever
  `E(|H| ∫_{[0,∞)} a dC) < ∞` (so that both sides are defined). -/
theorem remark_2_2 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (C : ℝ≥0 → Ω → ℝ) (hC_adapted : StronglyAdapted 𝓕 C)
    (hC_mono : ∀ ω, Monotone fun t => C t ω) (hC_cadlag : ∀ ω, IsCadlag fun t => C t ω)
    (hC_nonneg : ∀ ω, 0 ≤ C 0 ω)
    (a : ℝ≥0 → ℝ) (ha_meas : Measurable a) (ha_nonneg : ∀ s, 0 ≤ a s) :
    (∀ (H : Ω → ℝ), Measurable H → (∀ ω, 0 ≤ H ω) →
      ∀ (Hc : ℝ≥0 → Ω → ℝ≥0∞), (∀ t, Measurable[𝓕 t] (Hc t)) →
        (∀ t (B : Set Ω), MeasurableSet[𝓕 t] B →
          ∫⁻ ω in B, Hc t ω ∂P = ∫⁻ ω in B, ENNReal.ofReal (H ω) ∂P) →
        (∀ ω t, ContinuousWithinAt (fun s => Hc s ω) (Set.Ici t) t ∧
          (0 < t → ∃ l : ℝ≥0∞, Tendsto (fun s => Hc s ω) (𝓝[<] t) (𝓝 l))) →
        ∫⁻ ω, ENNReal.ofReal (H ω) *
            ∫⁻ s in Set.Ici (0 : ℝ), ENNReal.ofReal (a s.toNNReal)
              ∂measureFromZero (fun t => C t ω) ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Ici (0 : ℝ), Hc s.toNNReal ω * ENNReal.ofReal (a s.toNNReal)
              ∂measureFromZero (fun t => C t ω) ∂P) ∧
    (∀ (H : Ω → ℝ), Integrable H P →
      ∀ (Hc : ℝ≥0 → Ω → ℝ), (∀ ω, IsCadlag fun t => Hc t ω) →
        (∀ t : ℝ≥0, Hc t =ᵐ[P] MeasureTheory.condExp (𝓕 t) P H) →
        (∫⁻ ω, ‖H ω‖ₑ * ∫⁻ s in Set.Ici (0 : ℝ), ENNReal.ofReal (a s.toNNReal)
            ∂measureFromZero (fun t => C t ω) ∂P) < ⊤ →
        ∫ ω, H ω * ∫ s in Set.Ici (0 : ℝ), a s.toNNReal ∂measureFromZero (fun t => C t ω) ∂P =
          ∫ ω, ∫ s in Set.Ici (0 : ℝ), Hc s.toNNReal ω * a s.toNNReal
              ∂measureFromZero (fun t => C t ω) ∂P) := by sorry

end AntonelliBFSDE.Backward
