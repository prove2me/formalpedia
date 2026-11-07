-- Prove2me | Theorems.Thm_DynBrooks_proposition_5_5
-- name    : DynBrooks.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:37.903194+00:00
-- url     : https://prove2.me/theorems/29f7ada0-f3fd-4109-b105-9dbaa1bca935
-- title:
--   Proposition 5.5 — an attempt fails at depth $L$ with probability at most $12\,n\Delta^2\Delta^{-L/512}$
-- statement:
--   Fix a graph $G$ on $[n]$ of maximum degree at most $\Delta\ge16$ with no $K_{\Delta+1}$, a proper partial coloring $\chi_0$ with one hole $v_0$, and a stored neighbor array. For every positive integer $L$,
--
--   $$P[\text{one attempt fails at depth }L]\le C_0\,n\,\Delta^2\,\Delta^{-\varepsilon L},\qquad C_0=12,\ \varepsilon=1/512,$$
--
--   the probability being over the uniform moves of Algorithm 3 after the first (deterministic) move.
--
--   Choosing $L=\Theta(\log_\Delta n)$ makes one attempt succeed with high probability.
--
--   Differences from the source:
--   - generalization: the stored neighbor array of the data structure → every neighbor array; reason: the paper's array is one of them
--   - reading: test 4: 'v_i has two neighbors in X_{i−1}' → at least two neighbors in X_{i−1}; reason: with three or more earlier neighbors test 2 already succeeds (p.62)
--   - encoding: the probability that one attempt fails → the exact recursion of the attempt's law (failProb), an empty choice set counted as failure; reason: an empty choice set does not occur (Lemma 5.2); counting it as failure can only increase the probability
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Proposition 5.5, p.60 (PDF 62); standing assumptions §5, p.54 (PDF 56)

import Mathlib
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_Attempt

namespace DynBrooks

/-- **Proposition 5.5** (Failure probability of an attempt; Mishra, Mukherjee, *Fully Dynamic Brooks
Coloring*, STOC 2027 submission, sha256 6542a9f1…, p.60 (PDF 62)), under the standing assumptions of
§5, p.54 (maximum degree at most `∆ ≥ 16`, no `K_{∆+1}`). For every fixed initial proper partial
coloring with one hole, and every positive integer `L`,
`P[one attempt fails at depth L] ≤ C₀ n ∆² ∆^{−εL}`, with `C₀ = 12` and `ε = 1/512`.

**Formalization Note.** `failProb … L [v₀]` is the exact probability that Algorithm 3 with length limit
`L`, started at the hole `v₀`, returns failure: the first move is deterministic (the first non-twin
in the stored neighbor array, for every such array), and every later move is uniform on its choice set.
An empty choice set would count as failure; it does not occur. -/
theorem proposition_5_5 (n Δ : ℕ) (hΔ : 16 ≤ Δ) (G : SimpleGraph (Fin n)) (hG : IsBrooks Δ G)
    (χ₀ : Fin n → ℕ) (hχ : IsPartialColoring Δ G χ₀) (v₀ : Fin n) (hv₀ : HasOneHole χ₀ v₀)
    (nbr : Fin n → List (Fin n)) (hnbr : IsNeighborArray G nbr) (L : ℕ) (hL : 0 < L) :
    failProb Δ G χ₀ nbr v₀ L [v₀] ≤
      12 * (n : ℝ) * (Δ : ℝ) ^ 2 * (Δ : ℝ) ^ (-(1 / 512 : ℝ) * (L : ℝ)) := by sorry

end DynBrooks
