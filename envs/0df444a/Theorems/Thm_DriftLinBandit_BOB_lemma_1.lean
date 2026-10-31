-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_lemma_1
-- name    : DriftLinBandit.BOB.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:46.00664+00:00
-- url     : https://prove2.me/theorems/6e1f088c-7aae-4825-971e-2f713718dd5d
-- title:
--   Lemma 1, p. 16 — every block reward is at most Hν + 2R√(H ln(T/√H)) in absolute value with probability ≥ 1 − 2/T
-- statement:
--   Let an instance satisfy $|\langle x,\theta_t\rangle|\le\nu$ for all $t\in[T]$ and $x\in D_t$, for some $\nu>0$, and let the noises be i.i.d. centred and $R$-sub-Gaussian. Fix a block length $H$ with $1\le H\le T$ and arbitrary actions $X_t\in D_t$, and let
--   $$
--   M_i=\Big|\sum_{t=(i-1)H+1}^{iH\wedge T}\big(\langle X_t,\theta_t\rangle+\eta_t\big)\Big|
--   $$
--   be the absolute cumulative reward of block $i$. Then
--   $$
--   \Pr\Big(\forall i\in[\lceil T/H\rceil]:\ M_i\le H\nu+2R\sqrt{H\ln(T/\sqrt H)}\Big)\ge1-\frac2T .
--   $$
--
--   With $\nu=1$ this justifies the normalisation by $Q$ in BOB's EXP3 update (14): block rewards divided by $Q$ and shifted by $\tfrac12$ lie in $[0,1]$ with high probability.
--
--   **Formalization Note.** The statement bounds the probability of the complementary event (some block exceeds the bound) by $2/T$. $1\le H\le T$ is added: the page applies the lemma to BOB's $H$, and $H\le T$ keeps $\ln(T/\sqrt H)\ge0$ and the blocks meaningful.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 16, Lemma 1; Appendix D, p. 39

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Bob

namespace DriftLinBandit.BOB

open MeasureTheory Matrix

/-- Lemma 1 (p. 16). Suppose `|⟨x, θ_t⟩| ≤ ν` for all `t ∈ [T]` and `x ∈ D_t`, for some `ν > 0`, and
let the noise be i.i.d. centred `R`-sub-Gaussian. For any block length `1 ≤ H ≤ T` and any actions
`X_t ∈ D_t`, let `M_i = |∑_{t=(i−1)H+1}^{i·H∧T} (⟨X_t, θ_t⟩ + η_t)|` be the absolute cumulative
reward of block `i`. Then with probability at least `1 − 2/T`,
`M_i ≤ Hν + 2R √(H ln(T/√H))` for all blocks `i = 1, …, ⌈T/H⌉`. -/
theorem lemma_1 {d : ℕ} (I : Instance d) (R ν : ℝ) (hR : 0 < R) (hν : 0 < ν)
    (hνb : ∀ t ∈ Finset.Icc 1 I.T, ∀ x ∈ I.D t, |x ⬝ᵥ I.θ t| ≤ ν)
    (H : ℕ) (hH : 1 ≤ H) (hHT : H ≤ I.T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : ℕ → Ω → ℝ) (hη : IsSubGNoise P η R)
    (X : ℕ → Ω → (Fin d → ℝ)) (hXD : ∀ t ∈ Finset.Icc 1 I.T, ∀ ω, X t ω ∈ I.D t) :
    P {ω | ∃ i ∈ Finset.Icc 1 ⌈(I.T : ℝ) / (H : ℝ)⌉₊,
        (H : ℝ) * ν + 2 * R * Real.sqrt ((H : ℝ) * Real.log ((I.T : ℝ) / Real.sqrt H)) <
          |∑ t ∈ Finset.Icc (blockStart H i) (blockEnd H I.T i), (X t ω ⬝ᵥ I.θ t + η t ω)|} ≤
      ENNReal.ofReal (2 / (I.T : ℝ)) := by sorry

end DriftLinBandit.BOB
