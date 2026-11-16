-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_5_4
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:42:03.233494+00:00
-- url     : https://prove2.me/theorems/a8c80d8d-3a0b-49a0-b359-4f3e5895fd41
-- title:
--   Theorem 5.4 — efficiency dichotomy for every adversary
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, let $\delta=\varepsilon/100$ and $c=1/e-6\delta$. There is an integer $R>0$, depending only on $\varepsilon$, such that against every adversary, with probability $1$, one of the following holds for Algorithm 2:
--
--   1. $N_j<R$ for infinitely many blocks $j$, every player is eventually successful, and at each block boundary $t_j$ with $N_j<R$,
--   $$D(t_j)\ge A(t_j)-R\qquad\text{and}\qquad A(t_j)\le t_j+R;$$
--   2. $N_j\ge R$ for every block $j$ from some point onward, and
--   $$\liminf_{T\to\infty}\frac{D(T)+\delta A(T)}{T}\ge c.$$
--
--   No arrival-rate restriction is assumed: the adversary may be adaptive and inject arbitrarily large finite bursts.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: liminf_{T→∞} (D(T)+δA(T))/T ≥ c → for every c′ < c, eventually c′T ≤ D(T)+δA(T); reason: this is the liminf in the extended reals; a real liminf of an unbounded sequence would be a default value
--   - encoding: every player is eventually successful → every possible player that exists in the execution succeeds in some slot; reason: players are the countably many labelled initial players and batch members
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.18 / PDF p.19, Theorem 5.4 (proof printed pp.35–36 / PDF pp.36–37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 5.4 (Efficiency dichotomy; printed p.18 / PDF p.19). Fix `ε ∈ (0, 1/e)`,
`δ = ε/100`, `c = 1/e − 6δ`. There is an integer `R > 0`, depending only on `ε`, such that
against every adversary, with probability `1`, either (i) `N_j < R` for infinitely many blocks,
every player eventually succeeds, and `D(t_j) ≥ A(t_j) − R`, `A(t_j) ≤ t_j + R` at each such
block boundary; or (ii) `N_j ≥ R` for every block from some point on and
`liminf_{T→∞} (D(T) + δA(T))/T ≥ c`. -/
theorem theorem_5_4 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ R : ℕ, 0 < R ∧ EfficiencyDichotomy.{u} ε R := by sorry

end EliasGlobalClock.LowerBound.Supplement
