-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_lemma_C_3
-- name    : EliasGlobalClock.LowerBound.Supplement.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:38:54.741307+00:00
-- url     : https://prove2.me/theorems/7805f9e4-df05-43ea-874a-9b8f537cc3e7
-- title:
--   Lemma C.3 — tests in a window under the arrival cap
-- statement:
--   Fix $\varepsilon\in(0,1/e)$ and $\delta=\varepsilon/100$. There is $N_0$ such that the following holds for every adversary model for Algorithm 2 and every block $j\ge1$. Consider the window starting at $t_j$ with length $H=B\lceil16\,\mathrm{prd}(k_j)/\delta\rceil$, $k_j=\lceil\log_{1+\delta}N_j\rceil$, and a starting history $G\in\mathcal F_{t_j}$ on every continuation of which $N_j\ge N_0$ and the adversary injects at most $\lfloor\delta^2N_j\rfloor$ players during the window, i.e. $A(t_j+H)-A(t_j)\le\lfloor\delta^2N_j\rfloor$. With bad targets defined relative to $N_j$, conditionally on $\mathcal F_{t_j}$, on $G$:
--
--   1. the first test (in block $j$ or later) with target $(1+\delta)^{k_j}$ fails with probability at most $\delta$;
--   2. the probability that some test of a bad target, in a block of the window, succeeds is at most $\delta$.
--
--   Together these guarantee that the players of the window adopt a good transmission probability early and keep a non-bad one, which drives Lemma 5.2.
--
--   Differences from the source:
--   - generalization: an adaptive adversary that sees the complete history before the fresh transmission choices of each slot, with private randomness → arrival batches predictable for an arbitrary filtration ℱ; the fresh choices are i.i.d. uniform variables U(u,t), revealed at t+1 and independent of ℱ_t; reason: the source history filtration is one instance; a finer ℱ_t only enlarges the adversary class and the conditioning σ-algebra, and conditional bounds on a finer σ-algebra imply them on the history by the tower property
--   - encoding: a player transmits independently with probability p → the player transmits iff its fresh uniform U(u,t) < p; reason: a uniform variable below p has probability p; independence across players and slots is part of the model
--   - encoding: Q(0) initial players; arrivals during slot t−1 counted in A(t); arrivals wait until the next block boundary → a fixed q₀ initial players; the batch a(t) is delivered between transmission t−1 and t, charged to A(t)−A(t−1) and present in Q(t); every statement is for every q₀; reason: this fixes the boundary convention of the brief while keeping the identity Q(t)=Q(0)+A(t)−D(t) and the whole class of causal arrivals; the source treats Q(0) as a given number
--   - encoding: conditional probability given ℱ_(t_j) (on the stated event) → for every ℱ_(t_j)-measurable S inside the event, the probability integrated over S is bounded by the bound integrated over S; reason: this is the defining property of the conditional (generalized, [0,∞]-valued) expectation/probability; no integrability is assumed, so the Bochner default value 0 never enters
--   - encoding: for all sufficiently large N_j → ∃ N₀ (depending only on ε) such that the conclusions hold whenever N_j ≥ N₀ on G; reason: the threshold is fixed before the adversary and the history
--   - generalization: every window W_i of the partition w_1=0, w_(i+1)=w_i+H_i, starting at w_i = t_j with N_j sufficiently large → the window of length H(N_j) starting at every block boundary t_j (j ≥ 1) with N_j ≥ N₀; reason: every window of the source partition starts at a block boundary; the proof of Lemma C.4 uses windows started at an arbitrary block boundary
--   - encoding: the first test with target (1+δ)^(k_j) fails → the event that the test of the first block j′ ≥ j with Int(j′) = k_j fails, written so that it would be the whole event if no such block existed; reason: the source asserts that this test exists (within prd(k_j) blocks); the encoding does not let a missing test make the bound vacuous
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.31 / PDF p.32, Lemma C.3 (proof printed pp.31–32 / PDF pp.32–33); windows printed pp.14–15 / PDF pp.15–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis

open MeasureTheory ProbabilityTheory

universe u

namespace EliasGlobalClock.LowerBound.Supplement

/-- Lemma C.3 (Tests in a window; printed p.31 / PDF p.32). Fix `ε ∈ (0, 1/e)`. For all
sufficiently large `N_j` (`N_j ≥ N₀(ε)`): for every adversary model and every window starting
at a block boundary `t_j` with length `H = B⌈16 prd(k_j)/δ⌉`, `k_j = ⌈log_{1+δ} N_j⌉`, and every
starting history `G ∈ ℱ_{t_j}` on every continuation of which the adversary injects at most
`⌊δ² N_j⌋` players during the window, conditionally on `ℱ_{t_j}` on `G`:
(1) the first test (at or after block `j`) with target `(1+δ)^{k_j}` fails with probability at
most `δ`; (2) the probability that some test of a target that is bad relative to `N_j`
succeeds during the window is at most `δ`. -/
theorem lemma_C_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ N₀ : ℕ, ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
      (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ), IsAdversaryModel P ℱ U a →
      ∀ j, 1 ≤ j → ∀ G : Set Ω, MeasurableSet[ℱ (blockStart ε j)] G →
        (∀ ω ∈ G, N₀ ≤ blockPop ε q₀ a U j ω ∧
          arrAt a (blockStart ε j + windowLength ε (blockPop ε q₀ a U j ω)) ω -
              arrAt a (blockStart ε j) ω ≤
            Nat.floor (delta ε ^ 2 * blockPop ε q₀ a U j ω)) →
        ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S → S ⊆ G →
          P (S ∩ {ω | ∀ j', j ≤ j' → targetExp j' = ceilExp ε (blockPop ε q₀ a U j ω) →
              (∀ j'', j ≤ j'' → j'' < j' →
                targetExp j'' ≠ ceilExp ε (blockPop ε q₀ a U j ω)) →
              ¬ TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j'}) ≤
            ENNReal.ofReal (delta ε) * P S ∧
          P (S ∩ {ω | ∃ j', j ≤ j' ∧
              blockStart ε j' < blockStart ε j + windowLength ε (blockPop ε q₀ a U j ω) ∧
              IsBadTarget ε (blockPop ε q₀ a U j ω) (targetExp j') ∧
              TestSucceeds ε q₀ (pathArrivals a ω) (pathCoins U ω) j'}) ≤
            ENNReal.ofReal (delta ε) * P S := by sorry

end EliasGlobalClock.LowerBound.Supplement
