-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_8
-- name    : CorrKClust.BalancedPivot.lemma_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:48.972804+00:00
-- url     : https://prove2.me/theorems/d0bf31a4-8b39-468d-bc80-8df628c50e3f
-- title:
--   Lemma 7.8 — least-loaded cluster has bounded projected load
-- statement:
--   For every requested failure exponent $c'>0$, there is an absolute $C>0$ such that for every graph on $n\ge2$ vertices, every $k\ge1$, and every admissible history-dependent minimum-size rule, with probability at least $1-n^{-c'}$ the following holds simultaneously. For every nonempty set $S$ of output clusters present at T, every integer $T\le t\le n$, and every currently least-loaded output cluster b,
--   $$P_b(t)\le C\left(\mu(S)\ln n+\frac{n\ln^2n}{T}+\frac{|U|\ln n}{|S|}\right).$$
--   The projected load $P_b(t)$ sums final masses only of pivots already assigned by t; current minimality refers to actual arrivals. Both S and T may depend on the order. This is a simultaneous, unconditional probability estimate, with C uniform over graph, k and rule.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: every finite vertex set → vertex types V : Type (universe 0); reason: every finite vertex set is in bijection with Fin n : Type, and cost, OPT_k and the algorithm transfer along such bijections
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
--   - reading: assign to the cluster with minimal size, with ties unspecified → every history-dependent rule returning a minimum-current-size cluster; reason: the proof uses only minimality and the absolute constant must be uniform over these choices
--   - reading: with high probability for a suitably large constant exponent → for every c′ > 0, an absolute C(c′) gives failure probability at most n^(−c′); reason: increasing the internal c in the three concentration events on p. 34 gives any requested exponent; no dependence on the instance is introduced
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.8, p. 34, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.8, p. 34: an absolute constant for each requested failure exponent. -/
theorem lemma_7_8 : ∀ c' : ℝ, 0 < c' → ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → ∀ (k : ℕ) (hk : 0 < k) (ρ : TieRule V k), Admissible ρ →
    probability (fun σ : ArrivalOrder V => ∃ S : Finset (Fin k), S.Nonempty ∧
      S ⊆ presentClusters hk G ρ σ ∧ ∃ (t : ℕ) (b : Fin k),
      stopTime G k σ ≤ t ∧ t ≤ Fintype.card V ∧ LeastLoaded hk G ρ σ t b ∧
      C * ((maxProjected hk G ρ σ S : ℝ) * Real.log (Fintype.card V) +
        (Fintype.card V : ℝ) * Real.log (Fintype.card V) ^ 2 / stopTime G k σ +
        ((uncoveredAtStop G k σ).card : ℝ) * Real.log (Fintype.card V) / S.card) <
          (projectedLoad hk G ρ σ t b : ℝ)) ≤ Real.rpow (Fintype.card V : ℝ) (-c') := by sorry

end CorrKClust.BalancedPivot
