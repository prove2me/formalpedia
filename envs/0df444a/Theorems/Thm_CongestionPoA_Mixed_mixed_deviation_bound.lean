-- Prove2me | Theorems.Thm_CongestionPoA_Mixed_mixed_deviation_bound
-- name    : CongestionPoA.Mixed.mixed_deviation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:07:48.553877+00:00
-- url     : https://prove2.me/theorems/049d4a4a-7951-46b3-bdb2-2d0fedc66506
-- title:
--   Theorem 1, proof (mixed) — at a mixed Nash equilibrium, E[cᵢ] ≤ Σ_{e∈Pᵢ} (a_e(E[n_e]+1) + b_e)
-- statement:
--   Consider a congestion game with players $N$, facilities $E$ and linear latencies $f_e(k) = a_e k + b_e$, $a_e, b_e \ge 0$. Let $p$ be a mixed Nash equilibrium, and let $P = (P_1,\dots,P_n)$ be any pure strategy profile, $P_i \in \Sigma_i$. Write $\mathbb E[c_i]$ for the expected cost of player $i$ and $\mathbb E[n_e]$ for the expected number of users of facility $e$ under $p$. Then for every player $i$,
--   $$\mathbb E[c_i] \le \sum_{e \in P_i} \bigl(a_e(\mathbb E[n_e] + 1) + b_e\bigr).$$
--
--   This is the first step of the proof of Theorem 1 (PDF p. 3), the comparison of a player's equilibrium cost with the cost of switching to $P_i$, carried over to mixed equilibria as Sect. 5 (PDF p. 6) says the proof does.
--
--   **Formalization Note** The coefficients $a_e, b_e$ are explicit, with the hypothesis $f_e(k) = a_e k + b_e$ for all $e, k$. The mixed Nash equilibrium is `AGT.IsMixedNash` with payoffs $-c_i$, through `CongestionPoA.Mixed.IsMixedNash`.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1, proof (first display), applied to mixed profiles as in Sect. 5 (PDF p. 6)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
Theorem 1, proof (PDF p. 3), applied to mixed profiles as in Sect. 5 (PDF p. 6): the deviation
inequality. Let the latencies be `f_e(k) = a_e·k + b_e` with `a_e, b_e ≥ 0`, let `σ` be a mixed Nash
equilibrium and `P` a pure strategy profile. Then for every player `i`,
`E[cᵢ] ≤ Σ_{e∈Pᵢ} (a_e·(E[n_e] + 1) + b_e)`.

**Formalization Note.** The paper displays the pure case with identity latencies,
`cᵢ(A) = Σ_{e∈Aᵢ} n_e(A) ≤ Σ_{e∈Pᵢ} n_e(A₋ᵢ, Pᵢ) ≤ Σ_{e∈Pᵢ} (n_e(A) + 1)`; Sect. 5 says the proof of
Theorem 1 carries over to mixed equilibria. Here the latencies are the paper's affine ones (Sect. 2),
the coefficients are explicit binders, `E[·]` is under the product distribution of `σ`, and `P` is
feasible (`Pᵢ ∈ Σᵢ`), which is what makes switching to `Pᵢ` a legal deviation. -/
theorem mixed_deviation_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) (i : ι) :
    expCost G σ i ≤ ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by sorry

end CongestionPoA.Mixed
