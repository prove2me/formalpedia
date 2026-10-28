-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_13
-- name    : FakeUserRanking.FORC.lemma_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:19.891243+00:00
-- url     : https://prove2.me/theorems/aa786411-b1b8-41ee-bc91-c1064300f63c
-- title:
--   Lemma 13, p. 56 — Hoeffding bound 2exp(−2ε²η̂) for the cross-learned mean (1/η̂)(Σ_{i≤η₁} X_i + Σ_{i≤η₂} Y_i/2^ℓ)
-- statement:
--   **Lemma 13.** Fix an integer $\ell>0$ and $\eta_1,\eta_2\in\{0,1,\dots,T\}$, and let
--   $$\hat\eta=\eta_1+\frac{\eta_2}{2^\ell}.$$
--   Let $X_1,\dots,X_T$ and $Y_1,\dots,Y_T$ be $\{0,1\}$-valued random variables with mean $\mu$, all $2T$ of them independent. If $\hat\eta>0$, then for every $\varepsilon>0$,
--   $$\mathbb P\left(\left|\frac1{\hat\eta}\Big(\sum_{i=1}^{\eta_1}X_i+\sum_{i=1}^{\eta_2}\frac{Y_i}{2^\ell}\Big)-\mu\right|>\varepsilon\right)\le2\exp\!\big(-2\varepsilon^2\hat\eta\big).$$
--
--   This is the concentration bound behind FORC's cross-learned estimates $\hat r^{(\ell)}_i$ of (18), in which level-$\ell$ samples have weight $1$ and lower-level samples weight $2^{-\ell}$; it is used in the proof of Lemma 6 (Claim 1, (40)).
--
--   **Formalization Note.** The variables are indexed by `Fin T` (0-based), and the sums run over the first $\eta_1$ and $\eta_2$ indices. They live on a probability space $(\Omega,\nu)$, are measurable, take values in $\{0,1\}$ almost surely and have integral $\mu$, which makes them identically distributed. Joint independence is `iIndepFun` of the family indexed by `Fin T ⊕ Fin T`. Hoeffding's inequality itself is the platform theorem `Concentration.hoeffding_two_sided`.
--
--   Differences from the source:
--   - reading: two sequences of {0,1}-valued i.i.d. random variables X_1..X_T and Y_1..Y_T → all 2T variables jointly independent (iIndepFun on Fin T ⊕ Fin T), each {0,1}-valued with mean µ; reason: the proof applies Hoeffding to the X's and Y's together and Claim 1 builds them independent (paper.md Slip 4)
--   - encoding: {0,1}-valued random variables with mean µ → measurable functions, almost surely in {0,1}, with ∫ = µ; reason: random variables are measurable; a.s. values and the mean determine the Bernoulli(µ) law, so the variables are identically distributed
--   - encoding: indices 1..T; sums Σ_{i=1}^{η_1}, Σ_{i=1}^{η_2} → Fin T, 0-based; sums over indices i < η₁, i < η₂; reason: Lean convention; same instances
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 56, Lemma 13

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FakeUserRanking.FORC

/-- Lemma 13, p. 56: Hoeffding's inequality for the cross-learned weighted mean
`(1/η̂)(∑_{i ≤ η₁} X_i + ∑_{i ≤ η₂} Y_i / 2^ℓ)` with `η̂ = η₁ + η₂/2^ℓ`. -/
theorem lemma_13 {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (T : ℕ) (X Y : Fin T → Ω → ℝ) (μ : ℝ)
    (hindep : iIndepFun (Sum.elim X Y) ν)
    (hXmeas : ∀ i, Measurable (X i)) (hYmeas : ∀ i, Measurable (Y i))
    (hX01 : ∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1)
    (hY01 : ∀ i, ∀ᵐ ω ∂ν, Y i ω = 0 ∨ Y i ω = 1)
    (hXmean : ∀ i, ∫ ω, X i ω ∂ν = μ) (hYmean : ∀ i, ∫ ω, Y i ω ∂ν = μ)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η₁ η₂ : ℕ) (h₁ : η₁ ≤ T) (h₂ : η₂ ≤ T)
    (hη : 0 < (η₁ : ℝ) + η₂ / 2 ^ ℓ) (ε : ℝ) (hε : 0 < ε) :
    ν.real {ω | ε < |(1 / ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) *
        (∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₁), X i ω +
          ∑ i ∈ Finset.univ.filter (fun i : Fin T => (i : ℕ) < η₂), Y i ω / 2 ^ ℓ) - μ|}
      ≤ 2 * Real.exp (-2 * ε ^ 2 * ((η₁ : ℝ) + η₂ / 2 ^ ℓ)) := by sorry

end FakeUserRanking.FORC
