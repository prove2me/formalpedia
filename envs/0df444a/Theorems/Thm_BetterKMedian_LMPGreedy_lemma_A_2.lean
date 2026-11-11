-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_lemma_A_2
-- name    : BetterKMedian.LMPGreedy.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:21:42.757626+00:00
-- url     : https://prove2.me/theorems/7ba8efe3-7b6a-44ab-a6cd-26942438bdc5
-- title:
--   Lemma A.2 — the cost of Algorithm 1 w.r.t. $\hat f$ is at most $\sum_j(\sum_{i\ge j}\beta(r_{j,i},r_{j,i+1})+r_{j,n+1})$
-- statement:
--   For every admissible $\beta$, every instance, every $\hat f\ge0$, every execution of Algorithm 1 with opening cost $\hat f$ and every Appendix-A order, the output $S^\star$ satisfies
--   $$\sum_{j\in D}d(j,S^\star)+\hat f\,|S^\star|\le\sum_{j=1}^n\Bigl(\sum_{i=j}^n\beta(r_{j,i},r_{j,i+1})+r_{j,n+1}\Bigr).$$
--
--   Differences from the source:
--   - reading: a metric d(·,·) on D ∪ F (§2, p. 5) → a real pseudometric `d` on points `Fin N` (nonnegative, symmetric, zero diagonal, triangle inequality; distinct points may be at distance 0), clients and facilities `Finset (Fin N)` that may overlap; reason: the paper's own examples (Figures 1–3, pp. 8–10) place clients at distance 0 from facilities, so "metric" is read as pseudometric; a metric is a special case
--   - generalization: §2 standing assumption (3): 1 ≤ d(i,j) ≤ poly(|D|) for i ∈ F, j ∈ D (p. 5) → no such assumption: every instance; reason: (3) is introduced as a k-median reduction "as in [CGL+25, Lemma 2.1]", while the facility-location results are claimed for every UFL instance; the Lean statement covers all instances and specializes to those satisfying (3) (see INSIGHTS I1)
--   - encoding: an instance of UFL → `Instance` requires a facility whenever there is a client (`facilities_nonempty`); reason: with D ≠ ∅ and F = ∅ every solution has cost +∞ and OPT_f is undefined; the condition only excludes undefined cases
--   - encoding: Algorithm 1, a continuous increase of α with events (p. 8) → an execution `steps : List (Step I.N)` with `I.IsExecution β f̂ steps`: the processed events with their times, times start at 0 and never decrease, each event's condition holds when it is processed, no event condition holds at any time from the previous event time up to (excluding) the next, and A = ∅ at the end; reason: the continuous process is determined by its event times; every tie-breaking order is its own execution
--   - generalization: "while A ≠ ∅ … (if multiple events occur simultaneously, process them in an arbitrary order)" (p. 8) → an event whose condition still holds at the time of the previous event may also be processed after A has become empty; reason: the page leaves open whether pending simultaneous events are processed once A = ∅; `IsExecution` admits both readings, so the ∀-execution conclusions specialize to either
--   - encoding: β : ℝ²≥0 → ℝ≥0 (Definition 3.1) → `β : ℝ → ℝ → ℝ` with `IsAdmissibleBid β`, every property required on the nonnegative quadrant (nonnegativity there is Property 1); reason: Algorithm 1 and the program evaluate β only at nonnegative arguments; same functions on ℝ²≥0
--   - encoding: Algorithm 1 run with opening cost f̂ (in Appendix A, f̂ = ρ·f with ρ ≥ 1, f ≥ 0) → any `fhat` with `0 ≤ fhat`; reason: every f̂ ≥ 0 is ρ·(f̂/ρ); same values of f̂
--   - encoding: clients ordered 1, …, n = |D| by α⋆, ties by the order of the events in which they become inactive (p. 30) → any list `ord` with `I.IsAppendixAOrder steps ord`; client index j is position j (1-based) of `ord`, `rA` takes the paper's 1-based indices with column n + 1; reason: clients that become inactive in the same event may be listed in either order, as on the page; each such order is one the paper may fix
--   - encoding: "the cost (with respect to opening cost f̂) of a solution output by Algorithm 1" → `I.cost (I.output steps) + fhat * (I.output steps).card` for the output of the execution; reason: cost_{f̂}(S⋆) = Σ_j d(j, S⋆) + f̂|S⋆|
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Lemma A.2, printed pp. 30–31 (PDF 32–33)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_AppendixA

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Lemma A.2** (Buhai et al. 2026, printed pp. 30–31, PDF 32–33). The cost, with respect to the
opening cost `f̂`, of the output `S⋆` of every execution of Algorithm 1 is at most
`Σ_{j=1}^n (Σ_{i=j}^n β(r_{j,i}, r_{j,i+1}) + r_{j,n+1})`:
`Σ_{j ∈ D} d(j, S⋆) + f̂ · |S⋆| ≤ Σ_{j=1}^n charge_j`. -/
theorem lemma_A_2 (β : ℝ → ℝ → ℝ) (hβ : IsAdmissibleBid β) (I : Instance) (fhat : ℝ)
    (hfhat : 0 ≤ fhat) (steps : List (Step I.N)) (hE : I.IsExecution β fhat steps)
    (ord : List (Fin I.N)) (hord : I.IsAppendixAOrder steps ord) :
    I.cost (I.output steps) + fhat * (I.output steps).card ≤
      ∑ j ∈ Finset.Icc 1 ord.length, I.charge β steps ord j := by sorry

end BetterKMedian.LMPGreedy
