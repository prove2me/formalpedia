-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_claim_A_4
-- name    : BetterKMedian.LMPGreedy.claim_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:22:01.22728+00:00
-- url     : https://prove2.me/theorems/87e00e5c-729e-4c38-a799-7bb68e3fe6f1
-- title:
--   Claim A.4 — for a facility $i^\star$ and clients $D'$, $(r,d,\hat f)$ satisfies constraints (7)–(11)
-- statement:
--   For every admissible $\beta$, every instance, every $\hat f\ge0$, every execution of Algorithm 1 with opening cost $\hat f$, every Appendix-A order, every facility $i^\star\in F$ and every $D'\subseteq D$: re-index the clients of $D'$ as $1,\dots,|D'|$ keeping their order, with $|D'|+1$ standing for the original $n+1$, and set $d_k=d(i^\star,k)$. Then $(r,d,\hat f)$ satisfies constraints (7)–(11) of Definition 3.2 with $n=|D'|$.
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
--   - reading: "For some facility i⋆ ∈ F, consider any subset of clients D′ ⊆ D … The variables (r, d, f̂) satisfy constraints (7) to (11)" (in the proof, after "assume D′ ≠ ∅") → every facility `istar ∈ I.facilities` and every `D′ ⊆ I.clients`, including D′ = ∅ (then only f̂ ≥ 0 is asserted); reason: the claim is applied to each optimal facility and its clients (proof of Theorem 3.3); D′ = ∅ holds trivially
--   - encoding: the re-indexed variables (r, d) "supported on D′" → `I.subR steps ord D′` and `I.subD ord D′ istar` (`reindex` maps 1..|D′| to the indices of D′ in increasing order and |D′| + 1 to n + 1); reason: same variables
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Claim A.4, printed p. 31 (PDF 33), inside the proof of Lemma A.3

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Bidding
import Definitions.Def_BetterKMedian_LMPGreedy_FRProgram
import Definitions.Def_BetterKMedian_LMPGreedy_AppendixA

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Claim A.4** (Buhai et al. 2026, printed p. 31, PDF 33, inside the proof of Lemma A.3). For
every execution of Algorithm 1 with opening cost `f̂`, every Appendix-A order, every facility
`i⋆ ∈ F` and every set of clients `D′ ⊆ D`, re-indexed `1, …, |D′|` in the original order
(with `|D′| + 1` standing for the original `n + 1`) and with `d_k = d(i⋆, k)`, the variables
`(r, d, f̂)` satisfy constraints (7) to (11) of Definition 3.2. -/
theorem claim_A_4 (β : ℝ → ℝ → ℝ) (hβ : IsAdmissibleBid β) (I : Instance) (fhat : ℝ)
    (hfhat : 0 ≤ fhat) (steps : List (Step I.N)) (hE : I.IsExecution β fhat steps)
    (ord : List (Fin I.N)) (hord : I.IsAppendixAOrder steps ord)
    (istar : Fin I.N) (histar : istar ∈ I.facilities)
    (D' : Finset (Fin I.N)) (hD' : D' ⊆ I.clients) :
    FRConstraints β D'.card (I.subD ord D' istar) fhat (I.subR steps ord D') := by sorry

end BetterKMedian.LMPGreedy
