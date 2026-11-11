-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_4_1
-- name    : DoubleCorrRME.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:54.822262+00:00
-- url     : https://prove2.me/theorems/c1e6da11-4b0b-4c5f-b8c6-046d50abe1c7
-- title:
--   Lemma 4.1, p.20 — two stable references $S_1$ (samples) and $S_2$ (truncated batch means) exist w.p. $1-\delta$
-- statement:
--   Let the clean data $z_{i,j}$ ($i\in[N]$, $j\in[n]$) be $Nn$ i.i.d. draws from a law $P$ on $\mathbb R^d$ with mean $\mu$ and covariance $\Sigma\preceq I_d$, and let $m=Nn$, $L=\log(2/\delta)$ with $\delta\in(0,0.1)$. With the parameters of §4.1,
--
--   $$\alpha'=C_{\mathrm{ref}}\Big(\alpha+\frac{d+L}m\Big),\ \Delta=C_\Delta\sqrt{\alpha'},\ \kappa=1+\frac{\Delta^2}{\alpha'},\ \rho=C_\rho\sqrt\kappa\Big(\frac1{\sqrt n}+\sqrt{\frac{d+L}m}\Big),\ \lambda=\frac{\rho^2}\varepsilon,$$
--
--   for suitable universal constants and $\varepsilon,\alpha'$ sufficiently small, with probability at least $1-\delta$:
--
--   1. there is $\mathcal I\subseteq[N]\times[n]$ with $|\mathcal I|\ge(1-\alpha')Nn$ such that $S_1=\{z_{i,j}:(i,j)\in\mathcal I\}$ is $(\alpha',\Delta)$-stable with respect to $(\mu,I_d)$;
--   2. there is $\mathcal J\subseteq[N]$ with $|\mathcal J|\ge(1-\varepsilon/4)N$ such that $S_2=\{z^{\mathrm{tr}}_i:i\in\mathcal J\}$ is $(\varepsilon/4,C_S\rho)$-stable with respect to $(\bar z^{\mathrm{tr}},\lambda I_d)$, where $z^{\mathrm{tr}}$ is the truncation by the $\mathcal I$ of part 1.
--
--   These two references are what the two-level filter is analyzed against.
--
--   **Formalization Note** "With probability at least $1-\delta$ there exist" is a measurable set of clean datasets of probability at least $1-\delta$ on each of which $\mathcal I$ and $\mathcal J$ exist.
--
--   Differences from the source:
--   - encoding: the O(·) constants of §4.1 and O(ρ), "ε, α′ sufficiently small" → ∃ c, C_ref, C_∆, C_ρ, C_S > 0 before all data; ε < c, α′ ≤ c; reason: meaning of the universal constants
--   - reading: "with probability at least 1 − δ, there exist" → a measurable set of clean datasets of probability ≥ 1 − δ on which ℐ, 𝒥 exist; reason: avoids the probability of a possibly non-measurable event
--   - reading: Part 2's z^tr → built from Part 1's ℐ (Part 2 inside ∃ ℐ); reason: §2.3 defines z^tr from the ℐ of S_1
--   - generalization: α (implicit sign), N, n, d → 0 ≤ α, 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: α = 0 (no sample-level corruption) is admitted besides every α > 0 of Definition 1.1, and α enters only through α′, so the statement specializes to the paper's range; the averages need N, n ≥ 1
--   - encoding: Problem 1 law → IsBoundedCovLaw P (MemLp id 2 and covariance ⪯ I_d), cleanLaw = Nn i.i.d. copies; reason: the mean and covariance exist exactly under a finite second moment
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.1, p.20 (PDF p.21), with §4.1, p.20

import Mathlib
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params

open MeasureTheory

namespace DoubleCorrRME

/-- **Lemma 4.1** (two stable references), p.20 (PDF p.21), with the parameters of §4.1, p.20.

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 4.1. Let ε, α′ > 0 be sufficiently small. Then, with probability at least 1 − δ, there exist
two stable sets S_1 and S_2 with the following properties:
• Part 1. There exists ℐ ⊆ [N] × [n] such that |ℐ| ≥ (1 − α′)Nn and S_1 := {z_{i,j} : (i, j) ∈ ℐ}
is (α′, ∆)-stable with respect to (µ, I_d).
• Part 2. There exists 𝒥 ⊆ [N] with |𝒥| ≥ (1 − ε/4)N such that S_2 := {z^tr_i : i ∈ 𝒥} is
(ε/4, O(ρ))-stable with respect to (z̄^tr, λI_d)."

§4.1: "We let m := Nn and L := log(2/δ), for all δ ∈ (0, 0.1). We further define
α′ := O(α + (d+L)/m), ∆ := O(√α′), κ := 1 + ∆²/α′, ρ := O(√κ (1/√n + √((d+L)/m))), and
λ := ρ²/ε."

**Formalization Note.**
* The smallness constant `c`, the constants `C_ref, C_∆, C_ρ` of §4.1 and the constant `C_S` of
  "`O(ρ)`" are chosen before `N, n, d, ε, α, δ, P`. "ε, α′ sufficiently small" is `ε < c`,
  `α′ ≤ c`; `α ≥ 0` (it enters only through `α′`). `δ ∈ (0, 0.1)` is §4.1's standing range.
  `N, n, d ≥ 1`.
* The clean samples `z_{i,j}` are `Nn` i.i.d. draws from a law `P` of Problem 1 (finite second
  moment, mean `µ`, `Σ ⪯ I_d`). "With probability at least `1 − δ`, there exist": a measurable set of
  clean datasets of probability at least `1 − δ` on each of which `ℐ` and `𝒥` exist.
* Part 2's `z^tr` is built from Part 1's `ℐ` (§2.3, (1)), so Part 2 sits inside "∃ ℐ". -/
theorem lemma_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ Cref : ℝ, 0 < Cref ∧ ∃ CΔ : ℝ, 0 < CΔ ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
      ∃ CS : ℝ, 0 < CS ∧
      ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d → ∀ ε α δ : ℝ,
        0 < ε → ε < c → 0 ≤ α → 0 < δ → δ < 1 / 10 →
        let α' := alphaP Cref N n d α δ
        let Δ := deltaP CΔ α'
        let ρ := rhoP Cρ (kappaP α' Δ) N n d δ
        α' ≤ c →
        ∀ (P : Measure (Vec d)) [IsProbabilityMeasure P], IsBoundedCovLaw P →
          ∃ S : Set (Fin N → Fin n → Vec d), MeasurableSet S ∧
            ENNReal.ofReal (1 - δ) ≤ cleanLaw N n P S ∧
            ∀ z ∈ S, ∃ I : Finset (Fin N × Fin n),
              (1 - α') * ((N : ℝ) * n) ≤ I.card ∧
              IsStable (fun k : Fin N × Fin n => z k.1 k.2) I α' Δ (popMean P) 1 ∧
              ∃ J : Finset (Fin N), (1 - ε / 4) * (N : ℝ) ≤ J.card ∧
                IsStable (ztrBatch z I (popMean P)) J (ε / 4) (CS * ρ)
                  (ztrMean z I (popMean P)) (lambdaP ρ ε • 1) := by sorry

end DoubleCorrRME
