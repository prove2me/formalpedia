-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_2_2
-- name    : AvgValueAlloc.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:35.60097+00:00
-- url     : https://prove2.me/theorems/72964d3b-0b8f-4f61-adbc-2bf304a8b5a7
-- title:
--   Lemma 2.2 — Sponsor charging
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $\hat V$ a zero-at-zero monotone objective on banks with bank-coordinate diminishing returns, and $M=(v_1,\dots,v_m)$ funding items. Write $s_j$ and $H_{\hat V}(M)$ as in (6).
--
--   1. Exact greedy (a maximizing $j\in J(v)$, ties by smallest index; rejection if $J(v)=\emptyset$) attains
--   $$
--   W(X_g)+\hat V(B(X_g))\ \ge\ H_{\hat V}(M)/2 .
--   $$
--   2. Let a randomized causal rule choose recipients, and let $e_t$ be errors. If at every position $t$ and every past of positive probability the expected chosen increment is at least $\tfrac12\max_{j\in J(v_t)}s_j-\tfrac12e_t$ (rejection counts as increment $0$; the maximum over an empty set is $0$), then
--   $$
--   H_{\hat V}(M)\le 3\,\mathbb E\bigl[W+\hat V(B_g)\bigr]+\sum_t e_t .
--   $$
--
--   The first bound drives the history-trained and no-history branches; the second, with the softmax regret as $e_t$, drives the local branch.
--
--   Differences from the source:
--   - reading: zero-at-zero diminishing-returns objective → V̂(0) = 0, V̂ monotone and bank-coordinate DR on B ≥ 0; reason: the proof uses that f(X) = W(X) + V̂(B(X)) is monotone submodular, and without monotonicity the claim is false (n = 1, ρ = 1, one item v = 2, V̂(B) = −3B: greedy earns −1 < 0 = H/2); every objective the paper uses (G, Ĝ, G^s) is monotone by Lemma 2.1
--   - encoding: conditional expected chosen increment given the chosen past → Σ_o κ_t(X)(o)·s_o at every past of positive probability, with rejection scoring 0; reason: finite path law; same instances
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, Lemma 2.2, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_Hobj
import Definitions.Def_AvgValueAlloc_greedy
import Definitions.Def_AvgValueAlloc_pathProb

namespace AvgValueAlloc

/-- **Lemma 2.2 (Sponsor charging).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, Lemma 2.2, p.5: "Exact greedy attains at least H_V̂/2. If
the conditional expected chosen increment is at least half the maximum minus e_v/2, then
H_V̂ ≤ 3E[W + V̂(B_g)] + Σ_v e_v." Setting: (6), p.5.

For thresholds `ρ > 0`, a zero-at-zero monotone diminishing-returns objective `V̂` on banks and
funding items `M`:
1. exact greedy (least-index maximizer of `s_j` of (6), rejection when `J(v) = ∅`) satisfies
   `W(X_g) + V̂(B(X_g)) ≥ H_V̂(M)/2`;
2. for every randomized causal recipient rule `κ` and errors `e_t`, if at every position `t`
   and every past of positive probability the expected chosen increment is at least
   `max_{j ∈ J(v_t)} s_j/2 − e_t/2` (rejection counting as increment `0`), then
   `H_V̂(M) ≤ 3 E[W + V̂(B_g)] + Σ_t e_t`.

**Formalization Note.** The scores `s_j` are taken at the bank `B` earned by the past chosen
decisions; the maximum over an empty `J(v_t)` is `0`. -/
theorem lemma_2_2 {n m : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (V : (Fin n → ℝ) → ℝ)
    (hV : IsDRObjective V) (M : Fin m → Vec n) :
    Hobj ρ V M / 2 ≤ welfare M (greedy ρ V M) + V (routBank ρ M (greedy ρ V M)) ∧
      ∀ (κ : Fin m → (Fin m → Option (Fin n)) → Option (Fin n) → ℝ), IsCausalKernel ρ M κ →
        ∀ e : Fin m → ℝ,
          (∀ (t : Fin m) (X : Fin m → Option (Fin n)), 0 < pathPrefProb κ X t →
            maxScore ρ V (prefBank ρ M X t.val) (M t) / 2 - e t / 2 ≤
              ∑ o : Option (Fin n), κ t X o * o.elim 0 (score ρ V (prefBank ρ M X t.val) (M t))) →
          Hobj ρ V M ≤
            3 * ∑ X : Fin m → Option (Fin n),
                pathProb κ X * (welfare M X + V (routBank ρ M X)) + ∑ t, e t := by sorry

end AvgValueAlloc
