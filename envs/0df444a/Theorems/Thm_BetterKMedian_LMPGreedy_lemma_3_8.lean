-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_lemma_3_8
-- name    : BetterKMedian.LMPGreedy.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:55.729229+00:00
-- url     : https://prove2.me/theorems/9434c884-abd3-4e6c-89af-106c6dabd1da
-- title:
--   Lemma 3.8 — weak duality: the factor-revealing dual (Definition 3.7) upper-bounds the program of Definition 3.2 for $\beta_\gamma$
-- statement:
--   Let $\gamma\ge1$, $n\ge1$ and $V\in\mathbb R$. If for every choice of first bidding times $\tau_j\in\{j,\dots,n\}$ the inner program of Definition 3.7 has a feasible point of value $\rho\le V$, then every feasible point of the factor-revealing program of Definition 3.2 with $\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+$ has objective at most $V$.
--
--   Differences from the source:
--   - reading: β_γ(α, d) = [α − γd]⁺ in §B.1 (γ unconstrained in the statement) → hypothesis `1 ≤ γ`; reason: β_γ is used as an admissible bidding function (Definition 3.1 needs budget feasibility, i.e. γ ≥ 1), and the proof of Observation B.3 uses γ ≥ 1 ("whenever 0 ≤ b ≤ a and γ ≥ 1"); Theorem 3.6 applies it for γ ∈ [1, 1.224]
--   - encoding: variables d_j, f, r_{j,k} for 1 ≤ j ≤ k ≤ n + 1 (Definition 3.2) → functions `d : ℕ → ℝ`, `r : ℕ → ℕ → ℝ` and `f : ℝ`, constraints only on the paper's 1-based ranges; values outside them occur in no constraint and not in the objective; reason: same feasible points restricted to the index ranges
--   - encoding: first bidding times τ_j ∈ {j, …, n} for every client j → `τ : ℕ → ℕ` with `ValidTau n τ` (j ≤ τ j ≤ n for 1 ≤ j ≤ n); values at other indices unused; reason: same choices of τ
--   - encoding: "the optimum value of the factor-revealing dual (max over τ of min ρ) upper bounds the optimum value of the factor-revealing program" → for every n ≥ 1 and V: if every valid τ has a dual-feasible point with ρ ≤ V, every Definition 3.2 objective is ≤ V; reason: each inner minimum is attained when the inner program is feasible (a linear program whose objective ρ is bounded below by 0), so "max_τ min ρ ≤ V" is "every τ has a feasible ρ ≤ V"; an infeasible inner program makes the dual optimum +∞ and both statements empty
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Lemma 3.8, printed p. 16 (PDF 18); restated and proved p. 36 (PDF 38)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
import Definitions.Def_BetterKMedian_LMPGreedy_FRPrimalDual

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Lemma 3.8** (Buhai et al. 2026, printed p. 16, PDF 18; restated p. 36, PDF 38). The optimum
value of the factor-revealing dual (Definition 3.7) upper-bounds the optimum value of the
factor-revealing program (Definition 3.2) for `β_γ(α, d) = [α − γ · d]⁺`: for every `n ≥ 1` and
every `V`, if for every choice of first bidding times `τ_j ∈ {j, …, n}` the inner dual program
has a feasible point of value `ρ ≤ V`, then every feasible point of Definition 3.2 has objective
at most `V`. -/
theorem lemma_3_8 (γ : ℝ) (hγ : 1 ≤ γ) (n : ℕ) (hn : 1 ≤ n) (V : ℝ)
    (hdual : ∀ τ : ℕ → ℕ, ValidTau n τ →
      ∃ (ghat : ℕ → ℝ) (g s t : ℕ → ℕ → ℝ) (ρ : ℝ), DualFeasible n γ τ ghat g s t ρ ∧ ρ ≤ V) :
    ∀ (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ),
      FRFeasible (betaGamma γ) n d f r → frObjective (betaGamma γ) n f r ≤ V := by sorry

end BetterKMedian.LMPGreedy
