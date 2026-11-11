-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_theorem_3_3
-- name    : BetterKMedian.LMPGreedy.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:20:50.143352+00:00
-- url     : https://prove2.me/theorems/73bafc35-f1e7-4cd1-b614-915d8622eaf3
-- title:
--   Theorem 3.3 — a bound $\rho$ on the factor-revealing program makes Algorithm 1 with $\hat f=\rho f$ a $\rho$-LMP algorithm
-- statement:
--   Let $\beta$ be admissible and $\rho\ge1$ an upper bound on the optimal value of the factor-revealing program of Definition 3.2 over all $n\ge1$. Then on every UFL instance with opening cost $f$, Algorithm 1 run with $\beta$ and $\hat f=\rho f$ has an execution, and every execution outputs a solution $S^\star$ with
--   $$\sum_{j\in D}d(j,S^\star)\le\rho\,(\mathrm{OPT}_f-f\,|S^\star|).$$
--
--   Differences from the source:
--   - reading: a metric d(·,·) on D ∪ F (§2, p. 5) → a real pseudometric `d` on points `Fin N` (nonnegative, symmetric, zero diagonal, triangle inequality; distinct points may be at distance 0), clients and facilities `Finset (Fin N)` that may overlap; reason: the paper's own examples (Figures 1–3, pp. 8–10) place clients at distance 0 from facilities, so "metric" is read as pseudometric; a metric is a special case
--   - generalization: §2 standing assumption (3): 1 ≤ d(i,j) ≤ poly(|D|) for i ∈ F, j ∈ D (p. 5) → no such assumption: every instance; reason: (3) is introduced as a k-median reduction "as in [CGL+25, Lemma 2.1]", while the facility-location results are claimed for every UFL instance; the Lean statement covers all instances and specializes to those satisfying (3) (see INSIGHTS I1)
--   - encoding: an instance of UFL → `Instance` requires a facility whenever there is a client (`facilities_nonempty`); reason: with D ≠ ∅ and F = ∅ every solution has cost +∞ and OPT_f is undefined; the condition only excludes undefined cases
--   - encoding: Algorithm 1, a continuous increase of α with events (p. 8) → an execution `steps : List (Step I.N)` with `I.IsExecution β f̂ steps`: the processed events with their times, times start at 0 and never decrease, each event's condition holds when it is processed, no event condition holds at any time from the previous event time up to (excluding) the next, and A = ∅ at the end; reason: the continuous process is determined by its event times; every tie-breaking order is its own execution
--   - generalization: "while A ≠ ∅ … (if multiple events occur simultaneously, process them in an arbitrary order)" (p. 8) → an event whose condition still holds at the time of the previous event may also be processed after A has become empty; reason: the page leaves open whether pending simultaneous events are processed once A = ∅; `IsExecution` admits both readings, so the ∀-execution conclusions specialize to either
--   - encoding: β : ℝ²≥0 → ℝ≥0 (Definition 3.1) → `β : ℝ → ℝ → ℝ` with `IsAdmissibleBid β`, every property required on the nonnegative quadrant (nonnegativity there is Property 1); reason: Algorithm 1 and the program evaluate β only at nonnegative arguments; same functions on ℝ²≥0
--   - encoding: "ρ is an upper bound on the optimal value of the factor-revealing program in Definition 3.2 over all n ≥ 1" → `FRBoundedBy β ρ`: for every n ≥ 1, every feasible point (`FRFeasible`) has objective `frObjective` ≤ ρ; reason: no supremum is formed; an upper bound on the optimum is the same as a bound on every feasible point
--   - encoding: d(j, S) = min_{i∈S} d(i, j) with d(j, ∅) = +∞ (§2) → `distToSet S j` is the minimum for nonempty S and 0 for S = ∅; a solution must be nonempty when D ≠ ∅ (`IsFeasible`); reason: an empty S has infinite cost exactly when D ≠ ∅; feasibility encodes that, and the value at ∅ is never used by a feasible solution with clients
--   - encoding: OPT_f, the optimum value (§2) → `I.OPT`: the minimum of cost_f over the finite nonempty family of solutions; reason: same value
--   - reading: "Algorithm 1 run with facility cost f̂ = ρ·f is a ρ-LMP approximation algorithm" → (∃ an execution with f̂ = ρ * I.f) ∧ every such execution's output satisfies `IsLMPOutput ρ`; reason: an algorithm outputs a set on every instance (it terminates), and simultaneous events may be processed in any order (p. 8), so the guarantee is for every execution
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Theorem 3.3, printed p. 14 (PDF 16); restated p. 30 (PDF 32), proof pp. 32–33 (PDF 34–35)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
import Definitions.Def_BetterKMedian_LMPGreedy_Algorithm1

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Theorem 3.3** (Buhai et al. 2026, printed p. 14, PDF 16; restated p. 30, PDF 32). Let `β` be
an admissible bidding function and `ρ ≥ 1` an upper bound on the optimal value of the
factor-revealing program of Definition 3.2 over all `n ≥ 1`. Then Algorithm 1 run with facility
cost `f̂ = ρ · f` is a `ρ`-LMP approximation algorithm for UFL instances with facility cost `f`:
on every instance it has an execution, and every execution outputs a solution `S⋆` with
`Σ_{j ∈ D} d(j, S⋆) ≤ ρ · (OPT_f − f · |S⋆|)`. -/
theorem theorem_3_3 (β : ℝ → ℝ → ℝ) (hβ : IsAdmissibleBid β) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hFR : FRBoundedBy β ρ) (I : Instance) :
    (∃ steps : List (Step I.N), I.IsExecution β (ρ * I.f) steps) ∧
    ∀ steps : List (Step I.N), I.IsExecution β (ρ * I.f) steps →
      I.IsLMPOutput ρ (I.output steps) := by sorry

end BetterKMedian.LMPGreedy
