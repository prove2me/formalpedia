-- Prove2me | Theorems.Thm_BilateralRegret_lemma_1_eq3
-- name    : BilateralRegret.lemma_1_eq3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:43.853901+00:00
-- url     : https://prove2.me/theorems/bfe5bb3d-16c4-443a-847d-4240c8fd323a
-- title:
--   Lemma 1, eq. (3) — expected gain from trade via an independent uniform price
-- statement:
--   Let $S$ and $B$ be $[0,1]$-valued random variables, $p\in[0,1]$, and let $U$ be uniform on $[0,1]$ and independent of $(S,B)$. Then
--
--   $$
--   \mathbb E\big[\mathrm{GFT}(p,S,B)\big]=\mathbb P[S\le p\le U\le B]+\mathbb P[S\le U\le p\le B].
--   $$
--
--   The integrals of eq. (2) become probabilities of events that involve a uniformly random price, which a learner can sample by posting uniform prices.
--
--   Differences from the source:
--   - encoding: [0,1]-valued random variables S, B → measurable maps S, B on a probability space with S ω, B ω ∈ [0,1] for every ω; probabilities are real numbers (Measure.real); reason: Lean representation of random variables; same instances
--   - encoding: U uniform on [0,1] → U measurable with law P.map U = Lebesgue measure restricted to [0,1]; reason: definition of the uniform law
--   - encoding: U independent of (S, B) → IndepFun U (fun ω => (S ω, B ω)) P; reason: definition of independence of a random variable and a random pair
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Lemma 1, eq. (3), p.7 (proof p.21)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory ProbabilityTheory

/-- **Lemma 1, eq. (3).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §3, p.7.

Let `S`, `B` be `[0,1]`-valued random variables, `p ∈ [0,1]`, and let `U` be uniform on `[0,1]` and
independent of `(S, B)`. Then `𝔼[GFT(p, S, B)] = ℙ[S ≤ p ≤ U ≤ B] + ℙ[S ≤ U ≤ p ≤ B]`.

**Formalization Note.** "Uniform on `[0,1]`" is `P.map U = unif` (Lebesgue measure restricted to
`[0,1]`); independence is `IndepFun U (S, B)`. -/
theorem lemma_1_eq3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S B U : Ω → ℝ) (hSm : Measurable S) (hBm : Measurable B) (hUm : Measurable U)
    (hS : ∀ ω, S ω ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ ω, B ω ∈ Set.Icc (0 : ℝ) 1)
    (hU : P.map U = unif) (hind : IndepFun U (fun ω => (S ω, B ω)) P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, GFT p (S ω) (B ω) ∂P =
      P.real {ω | S ω ≤ p ∧ p ≤ U ω ∧ U ω ≤ B ω} + P.real {ω | S ω ≤ U ω ∧ U ω ≤ p ∧ p ≤ B ω} := by sorry

end BilateralRegret
