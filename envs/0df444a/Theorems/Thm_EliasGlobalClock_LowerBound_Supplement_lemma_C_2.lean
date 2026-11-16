-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_lemma_C_2
-- name    : EliasGlobalClock.LowerBound.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:38:17.629416+00:00
-- url     : https://prove2.me/theorems/d866dbb1-6b6f-4d6d-9cbe-525d2aa89770
-- title:
--   Lemma C.2 — conditional completeness and soundness of a single test
-- statement:
--   Fix $\varepsilon\in(0,1/e)$, $\delta=\varepsilon/100$, an adversary model for Algorithm 2 and a block $j\ge1$, whose test has target $M=(1+\delta)^{\mathrm{Int}(j)}$ and transmission probability $1/M$. Fix a reference population $N\ge4$ and a starting history at $t_j$, given as an $\mathcal F_{t_j}$-measurable event $G$, such that on every continuation in $G$ the number of participating players in each of the $m$ test slots lies in $[(1-\delta^2)N,(1+\delta^2)N]$. Conditionally on $\mathcal F_{t_j}$, on $G$:
--
--   1. if $M\in[N,(1+\delta)N]$, the test fails with probability at most $\delta$; in particular this holds when the target is $(1+\delta)^{\lceil\log_{1+\delta}N\rceil}$;
--   2. if $q_N(1/M)<1/e-3\delta$, the test succeeds with probability at most $\delta$; for this bad target $(1+\delta)^k$, $k=\mathrm{Int}(j)$, the success probability is also at most
--   $$\beta_k(N)=\delta^5\min\Big\{\sqrt{Np_k},\ (Np_k)^{-1/2}\Big\},\qquad p_k=(1+\delta)^{-k}.$$
--
--   Lemmas 5.1 and C.3 apply this estimate to every test of a window.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: conditional probability given ℱ_(t_j) (on the stated event) → for every ℱ_(t_j)-measurable S inside the event, the probability integrated over S is bounded by the bound integrated over S; reason: this is the defining property of the conditional (generalized, [0,∞]-valued) expectation/probability; no integrability is assumed, so the Bochner default value 0 never enters
--   - encoding: a starting history such that on every continuation the participant counts lie in [(1−δ²)N,(1+δ²)N] → an ℱ_(t_j)-measurable event G such that at every point of G the participant count of every test slot of block j lies in that range; reason: G is the union of such histories; the condition is required on every continuation, not almost surely
--   - encoding: a test with target M (and the target (1+δ)^⌈log_{1+δ}N⌉) → the test of block j of Algorithm 2, whose target is (1+δ)^Int(j); the particular target is the case Int(j) = ⌈log_{1+δ}N⌉; reason: the tests of Algorithm 2 are the tests the lemma is about; its target is determined by the block
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.30 / PDF p.31, Lemma C.2 (proof printed pp.30–31 / PDF pp.31–32); test and parameters printed pp.13, 29 / PDF pp.14, 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound.Supplement

/-- Lemma C.2 (Individual tests; printed p.30 / PDF p.31). Fix `ε ∈ (0, 1/e)`, an adversary
model, a block `j` with target `M = (1+δ)^{Int(j)}`, a reference population `N ≥ 4` and a
starting history `G ∈ ℱ_{t_j}` on every continuation of which every test slot of block `j`
has between `(1−δ²)N` and `(1+δ²)N` participants. Conditionally on `ℱ_{t_j}` on `G`:
(1) if `M ∈ [N, (1+δ)N]` the test fails with probability at most `δ`, in particular when
`M = (1+δ)^{⌈log_{1+δ} N⌉}`; (2) if `q_N(1/M) < 1/e − 3δ` the test succeeds with probability at
most `δ`, and at most `β_k(N)` for the (bad) target `(1+δ)^k`, `k = Int(j)`. Conditional
probabilities are stated by integrating over every `ℱ_{t_j}`-measurable `S ⊆ G`. -/
theorem lemma_C_2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ) (hmodel : IsAdversaryModel P ℱ U a)
    (j : ℕ) (hj : 1 ≤ j) (N : ℕ) (hN : 4 ≤ N)
    (G : Set Ω) (hG : MeasurableSet[ℱ (blockStart ε j)] G)
    (hpart : ∀ ω ∈ G, ∀ s, blockStart ε j ≤ s → s < blockStart ε j + testLength ε →
      (1 - delta ε ^ 2) * N ≤
          (participants ε q₀ (pathArrivals a ω) (pathCoins U ω) s : ℝ) ∧
        (participants ε q₀ (pathArrivals a ω) (pathCoins U ω) s : ℝ) ≤
          (1 + delta ε ^ 2) * N) :
    ((N : ℝ) ≤ (1 + delta ε) ^ targetExp j → (1 + delta ε) ^ targetExp j ≤ (1 + delta ε) * N →
      ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S → S ⊆ G →
        P (S ∩ {ω | ¬ TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j}) ≤
          ENNReal.ofReal (delta ε) * P S) ∧
    (targetExp j = ceilExp ε N →
      ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S → S ⊆ G →
        P (S ∩ {ω | ¬ TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j}) ≤
          ENNReal.ofReal (delta ε) * P S) ∧
    (singletonProb N (targetProb ε (targetExp j)) < Real.exp (-1) - 3 * delta ε →
      ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S → S ⊆ G →
        P (S ∩ {ω | TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j}) ≤
            ENNReal.ofReal (delta ε) * P S ∧
          P (S ∩ {ω | TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j}) ≤
            ENNReal.ofReal (betaBound ε (targetExp j) N) * P S) := by sorry

end EliasGlobalClock.LowerBound.Supplement
