-- Prove2me | Theorems.Thm_FairTeamContracts_theorem_3_2
-- name    : FairTeamContracts.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:09.679638+00:00
-- url     : https://prove2.me/theorems/9ae1ffc3-b59d-49e0-ac5d-1e49d00f2c8c
-- title:
--   Theorem 3.2 — optimality of the minimum share $\mathcal L^*_S$
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be submodular and fix a team $S$. Write $r_i=c_i/f(i\mid S\setminus\{i\})$ for the cut-off wages and
--
--   $$\mathcal L^*_S=\max_{i\in S}\Bigl\{r_i\cdot\frac{f(S\setminus\{i\})}{f(S)}\Bigr\}=\max_{i\in S}\Bigl\{r_i\cdot\frac{f(S)-f(i\mid S\setminus\{i\})}{f(S)}\Bigr\}.\qquad(2)$$
--
--   Then:
--
--   1. $\mathcal L^*_S\ge0$, and the two expressions in (2) agree;
--   2. if $S$ can be incentivized with shares at most $1$, i.e. $c_i\le f(i\mid S\setminus\{i\})$ for all $i\in S$, then the least $S$-incentive contract with minimum share $\mathcal L^*_S$, which pays $\max\{\mathcal L^*_S,r_i\}$ to each $i\in S$, is a fair team contract;
--   3. every fair team contract $(S,\alpha)$ pays each member at least that much, $\alpha_i\ge\max\{\mathcal L^*_S,r_i\}$ for $i\in S$, so its expected payment $\bigl(\sum_{i\in S}\alpha_i\bigr)f(S)$ is at least that of the minimum-share contract.
--
--   Hence a least $S$-incentive contract with a minimum share provides the least expected payment among all fair contracts that incentivize $S$, and the optimal share floor is the explicit quantity (2), computed from the $|S|+1$ values $f(S)$, $f(S\setminus\{i\})$ and the costs.
--
--   Differences from the source:
--   - generalization: the minimum-share contract has the least expected payments among fair contracts incentivizing S → additionally αᵢ ≥ max{𝓛*_S, rᵢ} for every fair (S, α) and every i ∈ S; reason: the per-agent bound implies the payment comparison, which is also stated
--   - encoding: there exists 𝓛 ≥ 0 such that the least S-incentive contract with minimum share 𝓛 is optimal among fair contracts incentivizing S → witness 𝓛 = minShare (eq. (2)) with 0 ≤ minShare; fairness of leastIncentive f c S (minShare f c S) when cᵢ ≤ f(i|S∖{i}) for all i ∈ S; payment comparison with every fair α; reason: the hypothesis cᵢ ≤ f(i|S∖{i}) holds exactly when some fair contract incentivizes S (shares are at most 1); otherwise the comparison is vacuous, as on the page
--   - reading: the optimal minimum share 𝓛*_S can be computed in polynomial time → minShare is the explicit maximum (2) of |S| expressions in the |S| + 1 value-oracle answers and the costs; no cost model; reason: no model of computation is formalized; the explicit formula is what the polynomial-time claim rests on
--   - encoding: rᵢ = cᵢ/f(i|S∖{i}) and f(S∖{i})/f(S) with 0/0 = 0, c/0 = ∞ → Lean division with x/0 = 0; reason: c/0 = ∞ arises only for cᵢ > 0 = f(i|S∖{i}), where no fair contract incentivizes S; f(S∖{i})/f(S) is 0/0 = 0 in both conventions when f(S) = 0
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 3.2 and eq. (2), p.11 (proof: p.12)

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_minShare
import Definitions.Def_FairTeamContracts_leastIncentive

namespace FairTeamContracts

/-- **Theorem 3.2 (Optimality of Minimum Share)** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 3.2 and
eq. (2), p.11; proof p.12). For a submodular success function `f`, nonnegative costs and any set
`S`, the least `S`-incentive contract with minimum share `𝓛*_S` (eq. (2)) has the least expected
payments among all fair team contracts that incentivize `S`. The clauses are:

1. `𝓛*_S ≥ 0`;
2. the two expressions of (2) agree:
   `max_{i∈S} rᵢ · f(S∖{i})/f(S) = max_{i∈S} rᵢ · (f(S) − f(i|S∖{i}))/f(S)`, `rᵢ` the cut-off wage;
3. if `S` can be incentivized at all (`cᵢ ≤ f(i | S∖{i})` for all `i ∈ S`, i.e. every cut-off
   wage is at most 1), the least `S`-incentive contract with minimum share `𝓛*_S` is a fair team
   contract;
4. every fair team contract `(S, α)` pays every `i ∈ S` at least `max{𝓛*_S, rᵢ}`, and its
   expected payment `(∑_{i∈S} αᵢ) f(S)` is at least that of the minimum-share contract.

**Formalization Note.** The paper's "`𝓛*_S` can be computed in polynomial time" is represented by
`minShare` being the explicit formula (2) in the `|S| + 1` value-oracle answers `f(S)`,
`f(S∖{i})` and the costs; no cost model is formalized. Lean's `x / 0 = 0` is used in `cutoff`
and in `f(S∖{i}) / f(S)`; see those definitions. -/
theorem theorem_3_2 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) :
    0 ≤ minShare f c S ∧
    minShare f c S = (if h : S.Nonempty then
        S.sup' h (fun i => cutoff f c S i * ((f S - marg f i S) / f S)) else 0) ∧
    ((∀ i ∈ S, c i ≤ marg f i S) → IsFair f c S (leastIncentive f c S (minShare f c S))) ∧
    (∀ α : Fin n → ℝ, IsFair f c S α →
      (∀ i ∈ S, max (minShare f c S) (cutoff f c S i) ≤ α i) ∧
      (∑ i ∈ S, leastIncentive f c S (minShare f c S) i) * f S ≤ (∑ i ∈ S, α i) * f S) := by sorry

end FairTeamContracts
