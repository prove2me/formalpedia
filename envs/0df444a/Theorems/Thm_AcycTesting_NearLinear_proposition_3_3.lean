-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_proposition_3_3
-- name    : AcycTesting.NearLinear.proposition_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:52.589223+00:00
-- url     : https://prove2.me/theorems/99fffd55-a05f-4679-8bae-03bb23629c1f
-- title:
--   Proposition 3.3 — conditional on G_γ, w.p. 1 − e^{−Ω(N)} every occurrence feedback set of Γ(Π) has ≥ 4N elements, and fas(Γ(Π)) ≥ 4N
-- statement:
--   There is an absolute constant $c>0$ such that for every girth scale $\gamma$ satisfying (3.1) and all sufficiently large even $N$ the following holds. Conditional on $G_\gamma$ (weak girth of $\Gamma(\Pi)$ greater than $\gamma$), with probability at least $1-e^{-cN}$, every set of occurrences whose deletion destroys all directed cycles of $\Gamma(\Pi)$ has at least $4N$ elements, and $\mathrm{fas}(\Gamma(\Pi))\ge4N$. In the statement this is written without division:
--   $$\Pr\big[G_\gamma\ \wedge\ \neg(\text{every occurrence feedback set has}\ge4N\text{ elements}\ \wedge\ \mathrm{fas}(\Gamma(\Pi))\ge4N)\big]\ \le\ e^{-cN}\,\Pr[G_\gamma].$$
--   This makes the random NO core far from acyclic.
--
--   Differences from the source:
--   - encoding: (3.1): an integer γ = γ(N) ≥ 2 with 64^γ log N = o(N) → GirthScale γ: γ : ℕ → ℕ, γ N ≥ 2 for all N, and 64^(γ N) · log N / N → 0; reason: the meaning of o(N) along N → ∞, natural log (§3.1)
--   - encoding: N even (standing assumption of §3.2), [N], colours [32] → Even N, Fin N, Fin 32 (0-based colours); reason: Lean convention; the same tuples
--   - encoding: Pr / E over independent uniform permutations π1, …, π32 → probU / expU: uniform on PermTuple N = Fin 32 → Equiv.Perm (Fin N); reason: the product of independent uniform laws is uniform on tuples
--   - encoding: with probability 1 − e^{−Ω(N)} conditional on Gγ → Pr[Gγ ∧ failure] ≤ e^{−cN} · Pr[Gγ]; reason: Pr[failure | Gγ] ≤ e^{−cN} multiplied by Pr[Gγ] > 0 (Proposition 3.1); no division
--   - reading: Ω(N) → ∃ c > 0 chosen before γ; the bound for all N ≥ N₀(γ); reason: the stronger reading (c absolute); the proof gives (1 − log 2)N − o(N)
--   - encoding: fas(Γ(Π)) of the simple graph Γ(Π) on Gγ, "in particular" → fas (coreGraph Π) (distinct outneighbours {π_a(v)}) inside the event, together with the occurrence clause; reason: on Gγ with γ ≥ 2 coreGraph Π is Γ(Π); stating both clauses keeps the "in particular"
--   - encoding: a set of occurrences whose deletion destroys all directed cycles → IsOccFeedbackSet: a Finset of occurrences (v, a) whose complement has no directed cycle, loops included; reason: the definition in the statement
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 15 (PDF 18), Proposition 3.3

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_PermCores

namespace AcycTesting.NearLinear

/-- Proposition 3.3 (farness of the conditioned core): one absolute constant `c > 0` such that,
under (3.1), for all large even `N`, conditional on `G_γ` the probability that some set of
fewer than `4N` occurrences destroys all directed cycles of `Γ(Π)`, or that `fas(Γ(Π)) < 4N`,
is at most `e^{-cN}` (written as `Pr[G_γ ∧ failure] ≤ e^{-cN} Pr[G_γ]`). -/
theorem proposition_3_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℕ → ℕ, GirthScale γ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        probU (fun πs : PermTuple N => CoreGirthGT (occMaps πs) (γ N) ∧
            ¬ ((∀ F : Finset (Fin N × Fin 32),
                  IsOccFeedbackSet (coreEnds (occMaps πs)) F → 4 * N ≤ F.card) ∧
                4 * N ≤ fas (coreGraph πs))) ≤
          Real.exp (-(c * N)) *
            probU (fun πs : PermTuple N => CoreGirthGT (occMaps πs) (γ N)) := by sorry

end AcycTesting.NearLinear
