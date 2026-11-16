-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_lemma_C_4
-- name    : EliasGlobalClock.LowerBound.Supplement.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:41:21.903206+00:00
-- url     : https://prove2.me/theorems/99aae395-3f71-4c50-9fc3-b6a0017101ad
-- title:
--   Lemma C.4 — exponential deviation bound for credited progress
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, $\delta=\varepsilon/100$, $c=1/e-6\delta$, and let $R$ be the threshold of Lemma 5.2 and Corollary 5.3. For every $\eta\in(0,c)$ there is a constant $a_{\varepsilon,\eta}>0$, depending only on $\varepsilon$ and $\eta$, such that for every adversary, every fixed deterministic block boundary $s$ and all sufficiently large integers $T$,
--   $$\Pr\Big(Q(t_j)\ge R\text{ at every block boundary }t_j\in[s,T],\ \ D(T)+\delta A(T)\le(c-\eta)T\Big)\le\exp\Big(-\frac{a_{\varepsilon,\eta}\,T}{\log^4(T+Q(0)+2)}\Big).$$
--
--   The logarithm is base $2$. The cutoff for "sufficiently large $T$" may depend on $s$ and $Q(0)$ but not on the adversary. Summed over $T$ and combined with the Borel–Cantelli lemma, this gives alternative (ii) of Theorem 5.4.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: R, the threshold from Corollary 5.3 → ∃ R satisfying the conclusions of Lemma 5.2 and Corollary 5.3 and the deviation bound; reason: this ties the lemma to the threshold fixed in §5.2
--   - reading: for every adversary, every fixed deterministic block boundary s, and all sufficiently large integers T → for every block boundary s and initial population Q(0) there is T₀ such that for every adversary and every T ≥ T₀; reason: ambiguous whether the cutoff may depend on the adversary; the proof gives a cutoff depending only on s, Q(0), ε and η, and the stronger reading is taken
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.33 / PDF p.34, Lemma C.4 (proof printed pp.33–35 / PDF pp.34–36); threshold R from Corollary 5.3, printed p.33 / PDF p.34; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Lemma C.4 (Deviation bound; printed p.33 / PDF p.34). With the threshold `R` of
Lemma 5.2 / Corollary 5.3: for every `η ∈ (0, c)` there is `a_{ε,η} > 0`, depending only on
`ε` and `η`, such that for every adversary, every deterministic block boundary `s` and all
sufficiently large integers `T`,
`Pr(Q(t_j) ≥ R for every block boundary t_j ∈ [s, T], D(T) + δA(T) ≤ (c − η)T)
  ≤ exp(−a_{ε,η} T / log⁴(T + Q(0) + 2))`. -/
theorem lemma_C_4 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ R : ℕ, WindowProgress.{u} ε R ∧ CappedWindowProgress.{u} ε R ∧
      ∀ η : ℝ, 0 < η → η < rateC ε →
        ∃ aε : ℝ, 0 < aε ∧ DeviationBound.{u} ε R η aε := by sorry

end EliasGlobalClock.LowerBound.Supplement
