-- Prove2me | Theorems.Thm_AntonelliBFSDE_BackwardForward_remark_2_2
-- name    : AntonelliBFSDE.BackwardForward.remark_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:14.665148+00:00
-- url     : https://prove2.me/theorems/f59fae9f-e364-4bb7-90a7-9207d33d3cc5
-- title:
--   Remark 2.2, (2.6) — E(H ∫_{[0,∞)} a dC) = E(∫_{[0,∞)} H_s a(s) dC_s) for the càdlàg version H_s of E(H | 𝓕_s)
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge 0},P)$ be a filtered probability space satisfying the usual hypotheses. Let $C$ be an adapted process whose paths are nondecreasing and càdlàg, with $C_0 \ge 0$ and the convention $C_{0-} = 0$, so that $dC_s(\omega)$ is a measure on $[0,\infty)$ with an atom of mass $C_0(\omega)$ at $0$. Let $a \ge 0$ be a Borel function on $\mathbb R_+$. Remark 2.2 states that
--   $$E\Big(H\int_{[0,\infty)} a(s)\,dC_s\Big) = E\Big(\int_{[0,\infty)} H_s\,a(s)\,dC_s\Big),$$
--   where $H_s$ is the càdlàg version of $E(H\mid\mathcal F_s)$, in two cases:
--
--   1. **Positive case.** $H \ge 0$ is a random variable, not necessarily integrable. Here $H_t$ takes values in $[0,\infty]$ and is the generalized conditional expectation: $H_t$ is $\mathcal F_t$-measurable and $E(H_t\,1_B) = E(H\,1_B)$ for every $B \in \mathcal F_t$. Its paths are right-continuous with left limits in $[0,\infty]$. The identity holds in $[0,\infty]$.
--   2. **$L^1$ case.** $H \in L^1(P)$, $H_t$ is a real càdlàg version of $E(H\mid\mathcal F_t)$, and $E(|H|\int_{[0,\infty)} a\,dC) < \infty$, so that both sides are defined. The identity holds in $\mathbb R$.
--
--   The remark is the case $X_t = a(t)H$ of the optional projection theorem (Lemma 2.1). The proof of Theorem 3.1 uses it with $C = D$ and $a \equiv 1$ ("by the optional projection theorem", pp. 787–788). There $\int_{[0,\infty)} dD = D_T$, because $D_0 = 0$ and $D$ is constant after $T$.
--
--   **Formalization Note** Time is $\mathbb R_{\ge 0}$. The measure $dC$ on $[0,\infty)$ is `measureFromZero`: the Stieltjes measure of $x \mapsto C_{x^+}$, which has no mass on $(-\infty,0]$, plus the atom $C_0\,\delta_0$. "Increasing" is read as nondecreasing paths with $C_0 \ge 0$, the Dellacherie–Meyer convention for increasing processes. In the positive case the version is $[0,\infty]$-valued and is characterized by its integrals over $\mathcal F_t$-sets, because Mathlib's `condExp` is defined only for integrable functions. In the $L^1$ case the finiteness hypothesis makes both Bochner integrals genuine and never junk values.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 779–780, Remark 2.2, (2.6)

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem remark_2_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (husual : UsualHypotheses 𝓕 P)
    (C : ℝ≥0 → Ω → ℝ) (hC_adapted : StronglyAdapted 𝓕 C)
    (hC_mono : ∀ ω, Monotone fun t => C t ω)
    (hC_cadlag : ∀ ω, AntonelliBFSDE.Backward.IsCadlag fun t => C t ω)
    (hC_nonneg : ∀ ω, 0 ≤ C 0 ω)
    (a : ℝ≥0 → ℝ) (ha_meas : Measurable a) (ha_nonneg : ∀ s, 0 ≤ a s) :
    (∀ H : Ω → ℝ, Measurable H → (∀ ω, 0 ≤ H ω) →
      ∀ Hc : ℝ≥0 → Ω → ℝ≥0∞,
        (∀ ω t, ContinuousWithinAt (fun s => Hc s ω) (Set.Ici t) t ∧
          (0 < t → ∃ l : ℝ≥0∞, Tendsto (fun s => Hc s ω) (𝓝[<] t) (𝓝 l))) →
        (∀ t, Measurable[𝓕 t] (Hc t) ∧ ∀ B : Set Ω, MeasurableSet[𝓕 t] B →
          ∫⁻ ω in B, Hc t ω ∂P = ∫⁻ ω in B, ENNReal.ofReal (H ω) ∂P) →
        ∫⁻ ω, ENNReal.ofReal (H ω) *
            ∫⁻ s in Set.Ici (0 : ℝ), ENNReal.ofReal (a s.toNNReal)
              ∂measureFromZero (fun t => C t ω) ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Ici (0 : ℝ), Hc s.toNNReal ω * ENNReal.ofReal (a s.toNNReal)
              ∂measureFromZero (fun t => C t ω) ∂P) ∧
    (∀ H : Ω → ℝ, Integrable H P →
      ∀ Hc : ℝ≥0 → Ω → ℝ, (∀ ω, AntonelliBFSDE.Backward.IsCadlag fun t => Hc t ω) →
        (∀ t : ℝ≥0, Hc t =ᵐ[P] P[H | 𝓕 t]) →
        (∫⁻ ω, ‖H ω‖ₑ * ∫⁻ s in Set.Ici (0 : ℝ), ENNReal.ofReal (a s.toNNReal)
            ∂measureFromZero (fun t => C t ω) ∂P) < ⊤ →
        ∫ ω, H ω * ∫ s in Set.Ici (0 : ℝ), a s.toNNReal ∂measureFromZero (fun t => C t ω) ∂P =
          ∫ ω, ∫ s in Set.Ici (0 : ℝ), Hc s.toNNReal ω * a s.toNNReal
              ∂measureFromZero (fun t => C t ω) ∂P) := by sorry

end AntonelliBFSDE.BackwardForward
