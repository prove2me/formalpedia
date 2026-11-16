-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_5_5
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:42:29.727436+00:00
-- url     : https://prove2.me/theorems/b01546e3-5409-452c-a3c1-f5fb50e138c2
-- title:
--   Theorem 5.5 — efficiency and eventual delivery against λ-adversaries
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, let $\delta=\varepsilon/100$, $c=1/e-6\delta$, and let $R$ be as in Theorem 5.4. A *λ-adversary* guarantees that, with probability $1$, $A(t)<\lambda t$ for infinitely many integers $t$ (arbitrary finite bursts are allowed). Against every λ-adversary with
--   $$0<\lambda<\frac{c}{1+\delta},$$
--   Algorithm 2 satisfies, with probability $1$:
--
--   1. $Q(t_j)<R$ at infinitely many block boundaries;
--   2. every player is eventually successful.
--
--   In particular, both conclusions hold whenever $0<\lambda\le 1/e-\varepsilon$.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - generalization: a λ-adversary injects players indefinitely and guarantees A(t) < λt for infinitely many t almost surely → only the almost-sure condition A(t) < λt for infinitely many t is assumed; reason: dropping “injects indefinitely” enlarges the adversary class; the source’s λ-adversaries are included
--   - encoding: let R be as in Theorem 5.4 → ∃ R > 0 for which the Theorem 5.4 dichotomy holds and both delivery claims hold; reason: this is how the shared threshold is expressed
--   - encoding: every player is eventually successful → every possible player that exists in the execution succeeds in some slot; reason: players are the countably many labelled initial players and batch members
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.18 / PDF p.19, Theorem 5.5 and the λ-adversary definition (proof printed pp.18–19 / PDF pp.19–20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 5.5 (Efficiency and eventual delivery; printed p.18 / PDF p.19). With `R` as in
Theorem 5.4 (the dichotomy holds for this `R`): against every λ-adversary with
`0 < λ < c/(1+δ)`, Algorithm 2 almost surely has `Q(t_j) < R` at infinitely many block
boundaries and every player eventually succeeds; in particular this holds for
`0 < λ ≤ 1/e − ε`. -/
theorem theorem_5_5 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ R : ℕ, 0 < R ∧ EfficiencyDichotomy.{u} ε R ∧
      (∀ lam : ℝ, 0 < lam → lam < rateC ε / (1 + delta ε) → LambdaDelivery.{u} ε R lam) ∧
      (∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) - ε → LambdaDelivery.{u} ε R lam) := by sorry

end EliasGlobalClock.LowerBound.Supplement
