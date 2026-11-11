-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_observation_B_3
-- name    : BetterKMedian.LMPGreedy.observation_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:59.410008+00:00
-- url     : https://prove2.me/theorems/86577b4b-a250-4e3b-b076-35c08663608d
-- title:
--   Observation B.3 — the family of inner primal LPs (Definition B.2) upper-bounds the factor-revealing program for $\beta_\gamma$
-- statement:
--   Let $\gamma\ge1$ and $n\ge1$. If, for every choice of first bidding times $\tau_j\in\{j,\dots,n\}$, every feasible point of the inner primal LP of Definition B.2 has objective at most $V$, then every feasible point of the factor-revealing program of Definition 3.2 with $\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+$ has objective at most $V$.
--
--   Differences from the source:
--   - reading: β_γ(α, d) = [α − γd]⁺ in §B.1 (γ unconstrained in the statement) → hypothesis `1 ≤ γ`; reason: β_γ is used as an admissible bidding function (Definition 3.1 needs budget feasibility, i.e. γ ≥ 1), and the proof of Observation B.3 uses γ ≥ 1 ("whenever 0 ≤ b ≤ a and γ ≥ 1"); Theorem 3.6 applies it for γ ∈ [1, 1.224]
--   - encoding: variables d_j, f, r_{j,k} for 1 ≤ j ≤ k ≤ n + 1 (Definition 3.2) → functions `d : ℕ → ℝ`, `r : ℕ → ℕ → ℝ` and `f : ℝ`, constraints only on the paper's 1-based ranges; values outside them occur in no constraint and not in the objective; reason: same feasible points restricted to the index ranges
--   - encoding: first bidding times τ_j ∈ {j, …, n} for every client j → `τ : ℕ → ℕ` with `ValidTau n τ` (j ≤ τ j ≤ n for 1 ≤ j ≤ n); values at other indices unused; reason: same choices of τ
--   - encoding: "the program above, defined as a maximization over a family of primal LPs, is an upperbound to the original FR program" → for every n ≥ 1 and V: every inner primal objective (every valid τ, every feasible point) ≤ V implies every Definition 3.2 objective ≤ V; reason: "optimum A ≤ optimum B" for two maximizations is exactly "every upper bound on B bounds A"; no supremum is formed
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Observation B.3, printed p. 35 (PDF 37)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
import Definitions.Def_BetterKMedian_LMPGreedy_FRPrimalDual

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Observation B.3** (Buhai et al. 2026, printed p. 35, PDF 37). The program of Definition B.2,
a maximization over the family of inner primal LPs indexed by the first bidding times, is an
upper bound to the factor-revealing program of Definition 3.2 for `β_γ(α, d) = [α − γ · d]⁺`:
for every `n ≥ 1` and every `V`, if every feasible point of every inner primal LP (every choice
of `τ_j ∈ {j, …, n}`) has objective at most `V`, then every feasible point of Definition 3.2 has
objective at most `V`. -/
theorem observation_B_3 (γ : ℝ) (hγ : 1 ≤ γ) (n : ℕ) (hn : 1 ≤ n) (V : ℝ)
    (hprimal : ∀ τ : ℕ → ℕ, ValidTau n τ →
      ∀ (r : ℕ → ℕ → ℝ) (d m : ℕ → ℝ) (ba bb : ℕ → ℕ → ℝ) (f : ℝ),
        PrimalFeasible n γ r d m ba bb f → primalObjective n γ τ r f ≤ V) :
    ∀ (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ),
      FRFeasible (betaGamma γ) n d f r → frObjective (betaGamma γ) n f r ≤ V := by sorry

end BetterKMedian.LMPGreedy
