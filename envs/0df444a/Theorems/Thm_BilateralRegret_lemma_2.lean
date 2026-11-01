-- Prove2me | Theorems.Thm_BilateralRegret_lemma_2
-- name    : BilateralRegret.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:42.724109+00:00
-- url     : https://prove2.me/theorems/c37fc204-5734-499a-9e13-d68d75384665
-- title:
--   Lemma 2 — $p\mapsto\mathbb E[\mathrm{GFT}(p,S,B)]$ is upper semicontinuous and has a maximizer $p^\star\in[0,1]$
-- statement:
--   Let $S$ and $B$ be $[0,1]$-valued random variables. Then:
--
--   1. the function $p\mapsto\mathbb E[\mathrm{GFT}(p,S,B)]$ is upper semicontinuous (on all of $\mathbb R$, with the formula of GFT);
--   2. there is a price $p^\star\in[0,1]$ with $\mathbb E[\mathrm{GFT}(p,S,B)]\le\mathbb E[\mathrm{GFT}(p^\star,S,B)]$ for every $p\in[0,1]$.
--
--   The best fixed price in hindsight therefore exists in expectation without any assumption on the joint law of $(S,B)$, so the regret is measured against an attained benchmark.
--
--   Differences from the source:
--   - encoding: [0,1]-valued random variables S, B → measurable maps S, B on a probability space with S ω, B ω ∈ [0,1] for every ω; probabilities are real numbers (Measure.real); reason: Lean representation of random variables; same instances
--   - generalization: the function p ↦ E[GFT(p, S, B)], GFT being defined for p ∈ [0,1], is upper semicontinuous → UpperSemicontinuous on all of ℝ with the formula of GFT; reason: the proof works with f, g : ℝ → [0,1] and p ∈ ℝ; restricting to [0,1] gives the statement on the price domain
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Lemma 2, App. B, p.22

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory

/-- **Lemma 2 (existence of the best price).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, App. B, p.22.

For `[0,1]`-valued random variables `S`, `B`, the function `p ↦ 𝔼[GFT(p, S, B)]` is upper
semicontinuous, and it has a maximizer `p★ ∈ [0,1]`.

**Formalization Note.** Upper semicontinuity is stated on all of `ℝ`, with `GFT`'s formula, as in the
paper's proof (`f, g : ℝ → [0,1]`, "for any `p ∈ ℝ`"). -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S B : Ω → ℝ) (hSm : Measurable S) (hBm : Measurable B)
    (hS : ∀ ω, S ω ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ ω, B ω ∈ Set.Icc (0 : ℝ) 1) :
    UpperSemicontinuous (fun p : ℝ => ∫ ω, GFT p (S ω) (B ω) ∂P) ∧
      ∃ pstar ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Set.Icc (0 : ℝ) 1,
        ∫ ω, GFT p (S ω) (B ω) ∂P ≤ ∫ ω, GFT pstar (S ω) (B ω) ∂P := by sorry

end BilateralRegret
