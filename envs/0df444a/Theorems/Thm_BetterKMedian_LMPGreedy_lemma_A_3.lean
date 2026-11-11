-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_lemma_A_3
-- name    : BetterKMedian.LMPGreedy.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:22:07.175194+00:00
-- url     : https://prove2.me/theorems/6c737901-c302-454f-a87b-0e4cb7a355e1
-- title:
--   Lemma A.3 — per-facility charging: $\sum_{j\in D'}(\dots)\le\hat f+\rho\sum_{j\in D'}d(j,i^\star)$
-- statement:
--   Let $\beta$ be admissible, $D'\subseteq D$, and $\rho\ge1$ an upper bound on the optimal value of the factor-revealing program of Definition 3.2 for $n=|D'|$. For every $\hat f\ge0$, every execution of Algorithm 1 with opening cost $\hat f$, every Appendix-A order and every facility $i^\star\in F$,
--   $$\sum_{j\in D'}\Bigl(\sum_{i=j}^n\beta(r_{j,i},r_{j,i+1})+r_{j,n+1}\Bigr)\le\hat f+\rho\sum_{j\in D'}d(j,i^\star),$$
--   where $j$ runs over the indices of the clients of $D'$ in the order and $n=|D|$.
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
--   - reading: "For some facility i⋆ ∈ F, consider any subset of clients D′ ⊆ D" → every facility `istar ∈ I.facilities` and every `D′ ⊆ I.clients`; reason: the lemma is applied to every optimal facility i⋆_ℓ with its clients D⋆_ℓ (proof of Theorem 3.3, p. 33); "for some" names an arbitrary facility
--   - generalization: "ρ ≥ 1 an upper bound on the optimal value of the factor-revealing program in Definition 3.2" (no n named) → only the program with n = |D′|: every point with `FRFeasible β D′.card` has `frObjective β D′.card` ≤ ρ; reason: Definition 3.2 is a family indexed by n and the proof uses only n = |D′|; the bound for every n (Theorem 3.3's hypothesis) implies the bound at n = |D′|, so the Lean statement specializes to the page's
--   - encoding: Σ_{j ∈ D′} over clients with their indices j in the order; d(j, i⋆) → sum over `I.positionsOf ord D′` of `I.charge β steps ord j`; `I.d x istar` summed over x ∈ D′; reason: same sums
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Lemma A.3, printed p. 31 (PDF 33)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
import Definitions.Def_BetterKMedian_LMPGreedy_AppendixA

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Lemma A.3** (Buhai et al. 2026, printed p. 31, PDF 33). Let `ρ ≥ 1` be an upper bound on the
optimal value of the factor-revealing program of Definition 3.2 (here only its instance with
`n = |D′|` is assumed: every feasible point has objective at most `ρ`). For every execution of
Algorithm 1 with opening cost `f̂ ≥ 0`, every Appendix-A order, every facility `i⋆ ∈ F` and every
subset of clients `D′ ⊆ D`:
`Σ_{j ∈ D′} (Σ_{i=j}^n β(r_{j,i}, r_{j,i+1}) + r_{j,n+1}) ≤ f̂ + ρ · Σ_{j ∈ D′} d(j, i⋆)`,
where `j` runs over the indices (positions in the order) of the clients of `D′` and `n = |D|`. -/
theorem lemma_A_3 (β : ℝ → ℝ → ℝ) (hβ : IsAdmissibleBid β) (I : Instance)
    (D' : Finset (Fin I.N)) (hD' : D' ⊆ I.clients) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hFR : ∀ (d : ℕ → ℝ) (f : ℝ) (r : ℕ → ℕ → ℝ),
      FRFeasible β D'.card d f r → frObjective β D'.card f r ≤ ρ)
    (fhat : ℝ) (hfhat : 0 ≤ fhat)
    (steps : List (Step I.N)) (hE : I.IsExecution β fhat steps)
    (ord : List (Fin I.N)) (hord : I.IsAppendixAOrder steps ord)
    (istar : Fin I.N) (histar : istar ∈ I.facilities) :
    ∑ j ∈ I.positionsOf ord D', I.charge β steps ord j ≤
      fhat + ρ * ∑ x ∈ D', I.d x istar := by sorry

end BetterKMedian.LMPGreedy
