-- Prove2me | Theorems.Thm_BilateralRegret_lemma_1_eq2
-- name    : BilateralRegret.lemma_1_eq2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:26.115967+00:00
-- url     : https://prove2.me/theorems/5772c7bf-92e4-4fbb-87f4-80014ec1ab74
-- title:
--   Lemma 1, eq. (2) — expected gain from trade as an integral of probabilities
-- statement:
--   Let $S$ and $B$ be $[0,1]$-valued random variables and $p\in[0,1]$. Then
--
--   $$
--   \mathbb E\big[\mathrm{GFT}(p,S,B)\big]=\int_{[p,1]}\mathbb P[S\le p\le\lambda\le B]\,d\lambda+\int_{[0,p]}\mathbb P[S\le\lambda\le p\le B]\,d\lambda .
--   $$
--
--   No independence between $S$ and $B$ is assumed. This identity is the starting point of the Lipschitz estimate and of the existence of a best price.
--
--   Differences from the source:
--   - encoding: [0,1]-valued random variables S, B → measurable maps S, B on a probability space with S ω, B ω ∈ [0,1] for every ω; probabilities are real numbers (Measure.real); reason: Lean representation of random variables; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Lemma 1, eq. (2), p.7 (proof p.21)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory

/-- **Lemma 1, eq. (2) (Decomposition lemma, expected form).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §3, p.7.

Let `S`, `B` be `[0,1]`-valued random variables and `p ∈ [0,1]`. Then
`𝔼[GFT(p, S, B)] = ∫_{[p,1]} ℙ[S ≤ p ≤ λ ≤ B] dλ + ∫_{[0,p]} ℙ[S ≤ λ ≤ p ≤ B] dλ`.

**Formalization Note.** Random variables are measurable maps on a probability space; "`[0,1]`-valued"
is read pointwise. Probabilities are real numbers (`Measure.real`). -/
theorem lemma_1_eq2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S B : Ω → ℝ) (hSm : Measurable S) (hBm : Measurable B)
    (hS : ∀ ω, S ω ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ ω, B ω ∈ Set.Icc (0 : ℝ) 1)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, GFT p (S ω) (B ω) ∂P =
      (∫ l in Set.Icc p 1, P.real {ω | S ω ≤ p ∧ p ≤ l ∧ l ≤ B ω})
        + ∫ l in Set.Icc 0 p, P.real {ω | S ω ≤ l ∧ l ≤ p ∧ p ≤ B ω} := by sorry

end BilateralRegret
