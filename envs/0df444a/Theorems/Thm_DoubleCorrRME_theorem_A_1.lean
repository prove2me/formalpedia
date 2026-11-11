-- Prove2me | Theorems.Thm_DoubleCorrRME_theorem_A_1
-- name    : DoubleCorrRME.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:09.364348+00:00
-- url     : https://prove2.me/theorems/bbbe0641-94cf-4823-a6a5-00ad50dd50fb
-- title:
--   Theorem A.1, p.63 — one-level robust mean estimation in $\tilde O(nd)$ time with error $O(\sqrt\Lambda(\sqrt\alpha+\sqrt{(d+\log(1/\delta))/n}))$ (corrected: $\log(1/\delta)\le c\cdot n$)
-- statement:
--   **Problem 2.** $n$ clean samples are drawn i.i.d. from a law on $\mathbb R^d$ with mean $\mu$ and covariance $\Sigma\preceq\Lambda I_d$; an adversary inspects them and replaces at most $\alpha n$ with arbitrary points.
--
--   There are universal constants $c,C,C_T>0$ and one program of the coin-tape real RAM such that for all $n,d\ge1$, $\alpha\in(0,c)$, $\delta\in(0,1)$ with $\log(1/\delta)\le c\,n$, and $\Lambda>0$, on input $(n,d,\Lambda,\alpha,\delta,X)$:
--
--   1. every run halts within $C_T\,nd\,\log^2(2+n+d+1/\delta)\log^2(2d)$ steps;
--   2. the output $\hat\mu$ is a measurable function of the coin tape;
--   3. for every such law and every such adversary, with probability at least $1-\delta$,
--
--   $$\|\hat\mu-\mu\|_2\le C\sqrt\Lambda\Big(\sqrt\alpha+\sqrt{\frac dn}+\sqrt{\frac{d+\log(1/\delta)}n}\Big).$$
--
--   This is the one-level estimator the main algorithm calls on flattened samples, on batch means, and on the weighted batch means.
--
--   **Formalization Note** The probability is the lower integral over the clean sample of the coin-tape probability, so it is meaningful for every adversary, measurable or not.
--
--   Differences from the source:
--   - correction: no sample-size condition → adds log(1/δ) ≤ c·n with the same universal c; reason: the printed statement is false: at d = n = Λ = 1 with no corruption (αn < 1), compare δ₀ with P₂ = 2δ·δ₀ + (1 − 2δ)·δ_M, M = (2δ(1 − 2δ))^{−1/2} (variance 1, mean ≥ 1/(2√δ) for δ ≤ 1/4); on input 0 the output must be within B = C(√α + 1 + √(1 + log(1/δ))) of 0 w.p. ≥ 1 − δ, so under P₂ the failure probability is ≥ 2δ(1 − δ) > δ once 1/(2√δ) > 2B, for every C as δ → 0; the added condition is log(1/q)/m ≤ c₀ of Lemma 3.1 = [PP25, Corollary 28], which Remark A.2 cites
--   - reading: "Algorithm 7 takes O(ndr log 𝒦 log²(2d)) time", r = O(log(nT log 𝒦/δ)), 𝒦 = O(dn/δ) → ∃ one admissible program of the coin-tape real RAM (input n, d, Λ, α, δ, X) halting on every input and tape within C_T·n·d·log²(2 + n + d + 1/δ)·log²(2d) steps; reason: the paper names no machine; r·log 𝒦 = O(log²(2 + n + d + 1/δ)) since 𝒦 = O(dn/δ) and T is polylogarithmic
--   - reading: "with probability at least 1 − δ" → lower integral over the clean sample of the coin-tape probability, for every adversary; the output is measurable in the tape; reason: meaningful for non-measurable adversaries; for a measurable adversary it is the joint probability
--   - encoding: Problem 2 with Σ ⪯ ΛI_d → IsCovLe Λ D (MemLp id 2, E⟨u, x − µ⟩² ≤ Λ∥u∥²); any map replacing at most αn points; reason: the mean and covariance exist exactly under a finite second moment; deterministic adversaries suffice
--   - encoding: "α sufficiently small", O(·), n, d → ∃ c, C, C_T > 0 before the instance; α < c; 1 ≤ n, 1 ≤ d; reason: meaning of the universal constants; n = 0 or d = 0 has no data
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Theorem A.1, p.63 (PDF p.64); Problem 2, p.62 (PDF p.63); Remark A.2, p.63

import Mathlib
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Machine
import Definitions.Def_DoubleCorrRME_InputLayout

open MeasureTheory

namespace DoubleCorrRME

/-- **Theorem A.1** (improved running time of [DHL19]), p.63 (PDF p.64), with Problem 2, p.62
(PDF p.63) — **corrected: `log(1/δ) ≤ c·n`**.

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Theorem A.1 (Improved running time of [DHL19]). Let α > 0 be sufficiently small, δ ∈ (0, 1), and
Λ > 0. Under Problem 2 with Σ ⪯ ΛI_d, Algorithm 7 takes O(ndr log 𝒦 log²(2d)) time and outputs µ̂
such that, with probability at least 1 − δ,
∥µ̂ − µ∥₂ ≤ O(√Λ (√α + √(d/n) + √((d + log(1/δ))/n))),
where r = O(log(nT log 𝒦/δ)) and 𝒦 = O(dn/δ)."

"Problem 2 (Standard Robust Mean Estimation). Let α ∈ (0, 1/2) and let P be a distribution over ℝ^d
with mean µ and covariance Σ ⪯ I_d. First, n clean samples X_1, …, X_n are drawn i.i.d. from P. An
adversary then inspects the samples and replaces at most αn of them with arbitrary points. Given only
the observed samples, the goal is to estimate µ in ℓ2 distance."

There are constants `c, C, C_T > 0` and one admissible program `P` such that for all `n, d ≥ 1`,
`α ∈ (0, c)`, `δ ∈ (0, 1)` with `log(1/δ) ≤ c·n` and `Λ > 0`, on input `(n, d, Λ, α, δ, X)`:
1. every coin tape and every dataset halts with `work ≤ C_T·n·d·log²(2 + n + d + 1/δ)·log²(2d)`;
2. the output is a measurable function of the tape;
3. for every law with finite second moment and `Σ ⪯ ΛI_d` and every adversary replacing at most
   `αn` points, `∥µ̂ − µ∥₂ ≤ C√Λ(√α + √(d/n) + √((d + log(1/δ))/n))` with probability at least
   `1 − δ` (lower integral over the clean sample of the tape probability).

**Formalization Note.**
* **Correction.** As printed, the statement has no sample-size condition and is false: at
  `d = n = Λ = 1` with no corruption (`αn < 1`), compare the point mass at `0` with
  `P₂ = 2δ·δ₀ + (1 − 2δ)·δ_M`, `M = (2δ(1 − 2δ))^{−1/2}` (variance `1`, mean `≥ 1/(2√δ)`). On input
  `0` the output must lie within `B = C(√α + 1 + √(1 + log(1/δ)))` of `0` with probability
  `≥ 1 − δ`, and under `P₂` the input is `0` with probability `2δ`, so the failure probability
  under `P₂` is at least `2δ(1 − δ) > δ` once `1/(2√δ) > 2B`; every `C` fails as `δ → 0`. The added
  hypothesis `log(1/δ) ≤ c·n` is the condition `log(1/q)/m ≤ c₀` of Lemma 3.1 (= [PP25,
  Corollary 28]), which Remark A.2 cites for the rate.
* The machine and the input layout `oneLevelInput` are a reading; the paper names none. `Λ` is an
  input, as in Algorithm 7's signature, so one program serves all `Λ`.
* Time: `r·log 𝒦 = O(log²(2 + n + d + 1/δ))` since `𝒦 = O(dn/δ)` and the number of rounds `T` is
  polylogarithmic; `2 +` keeps the logarithm positive. The bound holds on every input and tape.
* The adversary is any map of the clean sample, measurable or not; the lower integral `∫⁻` keeps
  the accuracy clause meaningful for every such map (for a measurable adversary it is the probability
  of the joint event). `P` has `MemLp id 2` (`IsCovLe Λ`). -/
theorem theorem_A_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ CT : ℝ, 0 < CT ∧ ∃ P : Program, Admissible P ∧
      ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → ∀ α δ Λ : ℝ, 0 < α → α < c → 0 < δ → δ < 1 → 0 < Λ →
        Real.log (1 / δ) ≤ c * n →
        (∀ (X : Fin n → Vec d) (ω : ℕ → Bool), ∃ t : ℕ,
          (run P (oneLevelInput n d Λ α δ X) ω t).halted = true ∧
          ((run P (oneLevelInput n d Λ α δ X) ω t).work : ℝ) ≤
            CT * n * d * Real.log (2 + n + d + 1 / δ) ^ 2 * Real.log (2 * d) ^ 2) ∧
        (∀ X : Fin n → Vec d, Measurable fun ω => output P d (oneLevelInput n d Λ α δ X) ω) ∧
        ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsCovLe Λ D →
          ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsSampleAdversary α A →
            ENNReal.ofReal (1 - δ) ≤
              ∫⁻ X, coinTape {ω | ‖output P d (oneLevelInput n d Λ α δ (A X)) ω - popMean D‖ ≤
                C * (Real.sqrt Λ * (Real.sqrt α + Real.sqrt ((d : ℝ) / n) +
                  Real.sqrt (((d : ℝ) + Real.log (1 / δ)) / n)))} ∂(Measure.pi fun _ : Fin n => D) := by sorry

end DoubleCorrRME
