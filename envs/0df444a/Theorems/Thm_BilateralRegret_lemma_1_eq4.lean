-- Prove2me | Theorems.Thm_BilateralRegret_lemma_1_eq4
-- name    : BilateralRegret.lemma_1_eq4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:43.628933+00:00
-- url     : https://prove2.me/theorems/de416dd7-b2f5-4122-a963-90034328e8d7
-- title:
--   Lemma 1, eq. (4) — the Decomposition lemma for independent $S$, $B$, $U$
-- statement:
--   Let $S$ and $B$ be $[0,1]$-valued random variables, $p\in[0,1]$, and let $U$ be uniform on $[0,1]$, with $S$, $B$, $U$ independent. Then
--
--   $$
--   \mathbb E\big[\mathrm{GFT}(p,S,B)\big]=\mathbb P[S\le p]\,\mathbb P[p\le U\le B]+\mathbb P[p\le B]\,\mathbb P[S\le U\le p].
--   $$
--
--   The factors $\mathbb P[S\le p]$ and $\mathbb P[p\le B]$ are local: they can be learned by posting the price $p$. The factors $\mathbb P[p\le U\le B]$ and $\mathbb P[S\le U\le p]$ are global: they can be learned by posting uniform prices. Scouting Bandits exploits exactly this split.
--
--   Differences from the source:
--   - encoding: [0,1]-valued random variables S, B → measurable maps S, B on a probability space with S ω, B ω ∈ [0,1] for every ω; probabilities are real numbers (Measure.real); reason: Lean representation of random variables; same instances
--   - encoding: U uniform on [0,1] → U measurable with law P.map U = Lebesgue measure restricted to [0,1]; reason: definition of the uniform law
--   - encoding: S, B, U are independent → mutual independence iIndepFun ![S, B, U] P; reason: definition of mutual independence of three random variables
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Lemma 1, eq. (4), p.7 (proof p.21)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory ProbabilityTheory

/-- **Lemma 1, eq. (4).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §3, p.7.

Let `S`, `B` be `[0,1]`-valued random variables, `p ∈ [0,1]`, and let `U` be uniform on `[0,1]`,
with `S, B, U` independent. Then
`𝔼[GFT(p, S, B)] = ℙ[S ≤ p] ℙ[p ≤ U ≤ B] + ℙ[p ≤ B] ℙ[S ≤ U ≤ p]`.

**Formalization Note.** "`S, B, U` are independent" is mutual independence, `iIndepFun ![S, B, U]`. -/
theorem lemma_1_eq4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S B U : Ω → ℝ) (hSm : Measurable S) (hBm : Measurable B) (hUm : Measurable U)
    (hS : ∀ ω, S ω ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ ω, B ω ∈ Set.Icc (0 : ℝ) 1)
    (hU : P.map U = unif) (hind : iIndepFun ![S, B, U] P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, GFT p (S ω) (B ω) ∂P =
      P.real {ω | S ω ≤ p} * P.real {ω | p ≤ U ω ∧ U ω ≤ B ω}
        + P.real {ω | p ≤ B ω} * P.real {ω | S ω ≤ U ω ∧ U ω ≤ p} := by sorry

end BilateralRegret
