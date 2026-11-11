-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_4_1
-- name    : AutobiddingGSP.Approximation.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:33.522192+00:00
-- url     : https://prove2.me/theorems/57e50c97-7b53-42c2-a667-93cb6074074a
-- title:
--   Lemma 4.1 — insertion probabilities form a distribution supported on legal positions
-- statement:
--   At an insertion step with $p=t-1$ earlier group bids, new bid $\beta=b_t(\alpha)$, the nonincreasing rearrangement $d$ of the earlier bids and Heaviside outputs $y_{t,j}$: (1) if every $y_{t,j}\in[0,1]$, then $\rho_{t,r}\ge0$ and $\sum_{r=0}^{t-1}\rho_{t,r}=1$; (2) if $y_{t,j}\in H(b_t-d_{t,j})$ for every $j$ (a fixed point), then $\rho_{t,r}>0\Rightarrow r\in R_t(\alpha)$.
--
--   Differences from the source:
--   - generalization: ρ_t ≥ 0 and ∑ρ_t = 1 for the circuit's Heaviside outputs → for every y ∈ [0,1]^{t−1}; reason: every Heaviside pseudogate output lies in [0,1]; the circuit's values are one instance
--   - generalization: bids b_s(α) = v_{g_s} α_{ι(g_s)} and steps t ≥ 2 → arbitrary real bids prev, β and every p = t − 1 ≥ 0; reason: the induced bids are one choice; p = 0 adds only the trivial one-position step
--   - encoding: 1-based steps t = 2, …, T and positions → 0-based steps t = 1, …, T − 1 (y j = y_{t,j+1}, d j = d_{t,j+1}); reason: Lean indexing; same objects
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 4.1, p. 13 (PDF 13)

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Insertion

namespace AutobiddingGSP.Approximation

/-- **Lemma 4.1** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 13 (PDF 13)). At insertion step `t`, with the `p = t − 1` earlier group
bids `prev`, their nonincreasing rearrangement `d` (the sorting network's output), the new group's
bid `β = b_t(α)` and the Heaviside outputs `y j = y_{t,j+1}`, the insertion probabilities
`ρ_t = (ρ_{t,0}, …, ρ_{t,t−1})` satisfy `ρ_{t,r} ≥ 0` and `∑_r ρ_{t,r} = 1`; moreover, at a fixed
point (`y_{t,j} ∈ H(b_t − d_{t,j})` for every `j`), `ρ_{t,r} > 0 ⟹ r ∈ R_t(α)`.

**Formalization Note** The first clause is stated for every `y ∈ [0, 1]^p` (the output range of
the Heaviside pseudogates), the second for every `y` satisfying the fixed-point relations. -/
theorem lemma_4_1 {p : ℕ} (prev : Fin p → ℝ) (β : ℝ) (d : Fin p → ℝ)
    (hd : IsDescRearrangement prev d) (y : Fin p → ℝ) :
    ((∀ j, 0 ≤ y j ∧ y j ≤ 1) → (∀ r, 0 ≤ insertProb y r) ∧ ∑ r, insertProb y r = 1) ∧
    ((∀ j, y j ∈ Hset (β - d j)) →
      ∀ r : Fin (p + 1), 0 < insertProb y r → IsLegal prev β r.val) := by sorry

end AutobiddingGSP.Approximation
