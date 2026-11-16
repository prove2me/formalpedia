-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_lemma_5_2
-- name    : EliasGlobalClock.LowerBound.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:39:40.30527+00:00
-- url     : https://prove2.me/theorems/7a9d2ac1-9c4e-42e4-a46f-9ea0a14ef4d1
-- title:
--   Lemma 5.2 — expected window progress at least cH
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, $\delta=\varepsilon/100$, $c=1/e-6\delta$. There is an integer $R$, depending only on $\varepsilon$, such that for every adversary model for Algorithm 2 and every window $W_i$ starting at a block boundary $w_i=t_j$ with $N_j\ge R$, of length $H_i=B\lceil16\,\mathrm{prd}(k_j)/\delta\rceil$,
--   $$\mathbb E\big[D_i+\delta A_i\ \big|\ \mathcal F_{w_i}\big]\ge cH_i,$$
--   where $A_i=A(w_i+H_i)-A(w_i)$ and $D_i=D(w_i+H_i)-D(w_i)$ are the arrivals and successes of the window. No restriction is placed on the arrivals.
--
--   This is the expected-progress estimate behind the potential-function argument of §5.2.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: conditional expectation given ℱ_(t_j) (on the stated event) → for every ℱ_(t_j)-measurable S inside the event, the expectation integrated over S is bounded by the bound integrated over S; reason: this is the defining property of the conditional (generalized, [0,∞]-valued) expectation/probability; no integrability is assumed, so the Bochner default value 0 never enters
--   - generalization: every window W_i of the partition w_1=0, w_(i+1)=w_i+H_i with N_j ≥ R → the window of length H(N_j) starting at every block boundary t_j (j ≥ 1) with N_j ≥ R; reason: every window of the source partition starts at a block boundary; the proof of Lemma C.4 uses windows started at an arbitrary block boundary
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.15 / PDF p.16, Lemma 5.2 (proof printed pp.32–33 / PDF pp.33–34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Lemma 5.2 (Window progress; printed p.15 / PDF p.16). For `ε ∈ (0, 1/e)` there is an
integer `R` depending only on `ε` such that, for every adversary and every window starting at
a block boundary `t_j` with `N_j ≥ R`, `E[D_i + δA_i | ℱ_{t_j}] ≥ c H_i`. -/
theorem lemma_5_2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ R : ℕ, WindowProgress.{u} ε R := by sorry

end EliasGlobalClock.LowerBound.Supplement
