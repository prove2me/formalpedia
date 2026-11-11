-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_10
-- name    : CorrKClust.BalancedPivot.lemma_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:52.356777+00:00
-- url     : https://prove2.me/theorems/8644f4b5-accd-4bda-8195-71dae70bb935
-- title:
--   Lemma 7.10 — groups without early pivots have few uncovered vertices
-- statement:
--   Fix a graph on $n\ge2$ vertices, a deterministic vertex set $Q\subseteq V$, an integer $1\le t\le n$, and a real $c>0$. Let $U_t$ be the vertices uncovered at t. Then
--   $$\Pr\!\left[\text{no pivot from }Q\text{ arrives by }t,\quad |Q\cap U_t|>\frac{cn\ln n}{t}\right]\le n^{-c}.$$
--   This covers the paper's optimal-partition block Q_j and dyadic time t = 2^i. Its proof uses neither clique density nor the dyadic form, so arbitrary fixed sets and valid times are included.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
--   - generalization: an almost-clique Q_j and time 2^i → every fixed vertex subset Q and every integer 1 ≤ t ≤ n; reason: the uncovered-count argument on p. 36 uses only that arrivals from uncovered Q vertices become pivots and specializes to the selected block and dyadic time
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.10, p. 36, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.10, p. 36, for arbitrary fixed sets and deterministic valid times. -/
theorem lemma_7_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (Q : Finset V) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ Fintype.card V)
    (c : ℝ) (hc : 0 < c) :
    probability (fun σ : ArrivalOrder V =>
      (¬ ∃ v ∈ Q, v ∈ pivots G σ ∧ arrivalTime σ v ≤ t) ∧
      c * Fintype.card V * Real.log (Fintype.card V) / t < ((Q ∩ uncovered G σ t).card : ℝ)) ≤
        Real.rpow (Fintype.card V : ℝ) (-c) := by sorry

end CorrKClust.BalancedPivot
