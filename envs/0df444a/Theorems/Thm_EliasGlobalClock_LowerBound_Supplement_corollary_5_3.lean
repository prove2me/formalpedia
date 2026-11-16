-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_corollary_5_3
-- name    : EliasGlobalClock.LowerBound.Supplement.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:40:34.683321+00:00
-- url     : https://prove2.me/theorems/fcecbbf5-c7a5-4473-91d9-574c3551cbff
-- title:
--   Corollary 5.3 — bounded window progress
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, $\delta=\varepsilon/100$, $c=1/e-6\delta$. There is an integer $R$, depending only on $\varepsilon$, for which both Lemma 5.2 holds and, under its conditions (every adversary model, every window starting at $w_i=t_j$ with $N_j\ge R$),
--   $$\mathbb E\big[Y_i\ \big|\ \mathcal F_{w_i}\big]\ge cH_i,\qquad Y_i=\min\{D_i+\delta A_i,\ H_i\}.$$
--
--   Capping each window's credited progress at its length makes the increments bounded, which the deviation bound of Lemma C.4 requires.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: conditional expectation given ℱ_(t_j) (on the stated event) → for every ℱ_(t_j)-measurable S inside the event, the expectation integrated over S is bounded by the bound integrated over S; reason: this is the defining property of the conditional (generalized, [0,∞]-valued) expectation/probability; no integrability is assumed, so the Bochner default value 0 never enters
--   - generalization: every window W_i of the partition w_1=0, w_(i+1)=w_i+H_i with N_j ≥ R → the window of length H(N_j) starting at every block boundary t_j (j ≥ 1) with N_j ≥ R; reason: every window of the source partition starts at a block boundary; the proof of Lemma C.4 uses windows started at an arbitrary block boundary
--   - encoding: with the same choice of R as in Lemma 5.2 → ∃ R for which both the Lemma 5.2 bound and the capped bound hold; reason: this is how the shared threshold is expressed
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.17 / PDF p.18, Corollary 5.3 (proof printed p.33 / PDF p.34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Corollary 5.3 (Bounded window progress; printed p.17 / PDF p.18). With the same choice of
`R` as in Lemma 5.2, `E[Y_i | ℱ_{t_j}] ≥ c H_i` for `Y_i = min{D_i + δA_i, H_i}`. -/
theorem corollary_5_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ R : ℕ, WindowProgress.{u} ε R ∧ CappedWindowProgress.{u} ε R := by sorry

end EliasGlobalClock.LowerBound.Supplement
