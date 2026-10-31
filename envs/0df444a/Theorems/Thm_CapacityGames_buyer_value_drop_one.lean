-- Prove2me | Theorems.Thm_CapacityGames_buyer_value_drop_one
-- name    : CapacityGames.buyer_value_drop_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:53.681667+00:00
-- url     : https://prove2.me/theorems/306b0100-cc9e-4618-8211-033ded37fdb5
-- title:
--   (A-3): under $\bar{\mathcal B}$, $\Pi^*_{\bar{\mathcal B}}(N\setminus\{i\})=\Pi^*_{\bar{\mathcal B}}(N)=\sum_j\Pi^*_{\mathcal C}(N\setminus\{j\})-(|N|-1)\Pi^*_{\mathcal C}(N)$
-- statement:
--   Consider a capacity game in which $\Pi^*_{\mathcal C}$ satisfies the submodularity inequalities (6). Let $\{\Delta_j\ge0\}$ be consistent with the costs (8) and let $\bar{\mathcal B}$ be the bids of Theorem 2. For a set $S$ of suppliers let $\Pi^*_{\bar{\mathcal B}}(S)$ be the buyer's optimal profit under $\bar{\mathcal B}$ over choices with $I(t)\subseteq S$. Then for every supplier $i\in N$ both maxima $\Pi^*_{\bar{\mathcal B}}(N\setminus\{i\})$ and $\Pi^*_{\bar{\mathcal B}}(N)$ are attained, and
--   $$\Pi^*_{\bar{\mathcal B}}(N\setminus\{i\})=\Pi^*_{\bar{\mathcal B}}(N)=\sum_{j\in N}\Pi^*_{\mathcal C}(N\setminus\{j\})-(|N|-1)\,\Pi^*_{\mathcal C}(N).\quad(\text{A-3})$$
--
--   Under the equilibrium bids the buyer loses nothing when any single supplier is excluded. This is the buyer's outside option against which a deviating supplier is measured on p.30.
--
--   Differences from the source:
--   - generalization: assumptions (a)–(c), p.8 (made "to ensure that the maxima exist and are attained") → not assumed; reason: consistency (8) with $\Delta\ge0$ already asserts that every maximum $\Pi^*_{\mathcal C}(S)$ is attained, which is all (a)–(c) are used for.
--   - generalization: proved under Assumptions 1–3 inside the proof of Theorem 2 → without Assumptions 1 and 2; reason: (A-3) does not use them.
--   - generalization: $\{\Delta_i\ge0: i\in N^*(\mathcal C)\}$ consistent → $\Delta_i\ge0$ on $\mathbf T$ for every $i\in N$, consistent; reason: the paper's family extended by $0$ is one, and $\bar{\mathcal B}$ reads $\Delta$ only on $N^*(\mathcal C)$.
--   - generalization: (8) attained at $t^*_S$ → attained at some supply chain optimal choice for $S$; reason: the weaker hypothesis gives the stronger statement.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$, $C_i(s(D))$, $P_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them.
--   - encoding: $\max$ in $\Pi^*_{\bar{\mathcal B}}$, $|N|-1$ → supremum together with the statement that it is attained, $|N|-1$ computed in $\mathbb R$; reason: Lean convention, same value.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, App. A.5, (A-3), p.29

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **Dropping one supplier costs the buyer nothing under the equilibrium bids**, display (A-3),
arXiv:1905.11084v1, App. A.5, p.29: under submodularity (6), for a family `Δ ≥ 0` consistent
with the costs and the bids `B̄` of Theorem 2, for every supplier `i`,
`Π*_B̄(N ∖ {i}) = Π*_B̄(N) = Σ_{j∈N} Π*_C(N ∖ {j}) − (|N| − 1) Π*_C(N)`,
and both maxima are attained.

**Formalization Note.** `Π*_B̄(S)` is an `sSup`; the first two conjuncts say that it is the
maximum of the buyer's values over `I(t) ⊆ N ∖ {i}` and over all of `N`. `|N| − 1` is computed in
`ℝ`.

The semicontinuity assumptions (a)–(c), p.8, are not imposed: consistency (8) with `Δ ≥ 0`
already says that every maximum `Π*_C(S)` is attained. -/
theorem buyer_value_drop_one {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (hsub : LocalSubmodular (scOptValue G))
    (Δ : N → (N → ℝ) → ℝ) (hΔ : ∀ i, ∀ t ∈ G.capSet, 0 ≤ Δ i t) (hcons : Consistent G Δ)
    (i : N) :
    IsGreatest (buyerValues G (barBids G Δ) (Finset.univ.erase i))
        (buyerOptValue G (barBids G Δ) (Finset.univ.erase i)) ∧
      IsGreatest (buyerValues G (barBids G Δ) Finset.univ)
        (buyerOptValue G (barBids G Δ) Finset.univ) ∧
      buyerOptValue G (barBids G Δ) (Finset.univ.erase i) =
        buyerOptValue G (barBids G Δ) Finset.univ ∧
      buyerOptValue G (barBids G Δ) Finset.univ =
        ∑ j, scOptValue G (Finset.univ.erase j) -
          ((Fintype.card N : ℝ) - 1) * scOptValue G Finset.univ := by sorry

end CapacityGames
