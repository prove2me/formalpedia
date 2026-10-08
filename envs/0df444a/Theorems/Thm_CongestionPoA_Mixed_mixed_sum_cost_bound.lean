-- Prove2me | Theorems.Thm_CongestionPoA_Mixed_mixed_sum_cost_bound
-- name    : CongestionPoA.Mixed.mixed_sum_cost_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:07:37.658982+00:00
-- url     : https://prove2.me/theorems/bcabbd98-8065-4d6f-a6e8-df7c758a26b8
-- title:
--   Theorem 1, proof (mixed) — Σᵢ E[cᵢ] ≤ Σ_e n_e(P)(a_e(E[n_e]+1) + b_e)
-- statement:
--   Consider a congestion game with players $N$, facilities $E$ and linear latencies $f_e(k) = a_e k + b_e$, $a_e, b_e \ge 0$. Let $p$ be a mixed Nash equilibrium and $P$ any pure strategy profile. Write $\mathbb E[c_i]$ and $\mathbb E[n_e]$ for the expected cost of player $i$ and the expected load of facility $e$ under $p$, and $n_e(P)$ for the number of players using $e$ in $P$. Then the mixed social cost satisfies
--   $$\mathrm{SUM}(p) = \sum_{i \in N} \mathbb E[c_i] \le \sum_{e \in E} n_e(P)\bigl(a_e(\mathbb E[n_e] + 1) + b_e\bigr).$$
--
--   This is the second step of the proof of Theorem 1 (PDF p. 3), summing the deviation inequality over the players and regrouping by facility, carried over to mixed equilibria as Sect. 5 (PDF p. 6) says the proof does.
--
--   **Formalization Note** The coefficients $a_e, b_e$ are explicit, with the hypothesis $f_e(k) = a_e k + b_e$ for all $e, k$. The mixed Nash equilibrium is `AGT.IsMixedNash` with payoffs $-c_i$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1, proof (second display), applied to mixed profiles as in Sect. 5 (PDF p. 6)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
Theorem 1, proof (PDF p. 3), applied to mixed profiles as in Sect. 5 (PDF p. 6): the summing step.
Let the latencies be `f_e(k) = a_e·k + b_e` with `a_e, b_e ≥ 0`, let `σ` be a mixed Nash equilibrium
and `P` a pure strategy profile. Then
`Σᵢ E[cᵢ] ≤ Σ_{e∈E} n_e(P)·(a_e·(E[n_e] + 1) + b_e)`.

**Formalization Note.** The paper displays the pure case with identity latencies,
`SUM(A) = Σ_{i∈N} cᵢ(A) ≤ Σ_{i∈N} Σ_{e∈Pᵢ} (n_e(A) + 1) = Σ_{e∈E} n_e(P)(n_e(A) + 1)`; Sect. 5 says the
proof of Theorem 1 carries over to mixed equilibria. Here the latencies are the paper's affine ones
(Sect. 2) with explicit coefficients, `E[·]` is under the product distribution of `σ`, the left side is
the mixed social cost `mixedSumCost G σ = Σᵢ E[cᵢ]` of Sect. 5, and `P` is feasible. -/
theorem mixed_sum_cost_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (expLoad G σ e + 1) + b e) := by sorry

end CongestionPoA.Mixed
