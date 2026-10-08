-- Prove2me | Theorems.Thm_DermanSeqDecisions_Ratio_theorem_3
-- name    : DermanSeqDecisions.Ratio.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:46:20.849489+00:00
-- url     : https://prove2.me/theorems/d7239ccd-8810-4e1d-b44c-d9445ab6167d
-- title:
--   Theorem 3 — under Assumption A a deterministic stationary procedure minimizes the ratio criterion over all procedures
-- statement:
--   Consider a controlled Markov chain with finitely many states $0, \dots, L$ and decisions $d_1, \dots, d_K$, all available in every state, with transition probabilities $q_{ij}(k)$. Let $w'_{ik} > 0$ and $w''_{ik} > 0$ be two sets of expected costs. For a procedure $R$ (history-dependent and randomized) started at $X_0 = i$, let $W'_t$ and $W''_t$ be the expected costs at time $t$ and
--   $$\psi_R(i) = \limsup_{T\to\infty} \frac{\sum_{t=0}^T W'_t}{\sum_{t=0}^T W''_t}.$$
--   Assume Assumption A: for every stationary randomized procedure all states belong to the same class. Then for every initial state $i$ there is a deterministic stationary procedure $R_3 \in C''$ with
--   $$\psi_{R_3}(i) = \min_{R \in C} \psi_R(i),$$
--   that is, $\psi_{R_3}(i) \le \psi_R(i)$ for every procedure $R \in C$.
--
--   The theorem shows that optimizing the ratio criterion over the stationary procedures, which the preceding display turns into a fractional linear program, already gives a procedure that is optimal over all procedures.
--
--   **Formalization Note** The quantifier order is "for every $i$ there is $R_3$", following the proof, which fixes $X_0 = i$ first. The competitors range over all history-dependent randomized procedures. The costs are explicit real arguments; the nonnegative cost field of Sennott's model plays no role.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 23, Theorem 3

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **Theorem 3** (Derman, *On Sequential Decisions and Markov Chains*, Management Science
9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, p. 23): "Under assumption A, there exists a
procedure `R₃ ε C″` such that `ψ_{R₃}(i) = min_{R ε C} ψ_R(i)`."

Let `w′ > 0` and `w″ > 0` be two sets of expected costs and assume Assumption A (every
stationary randomized procedure makes all states communicate). Then for every initial state `i`
there is a deterministic stationary procedure `f ∈ C″` whose ratio criterion
`ψ_f(i) = lim sup_T (∑_{t≤T} W′_t)/(∑_{t≤T} W″_t)` is at most `ψ_θ(i)` for every procedure
`θ ∈ C`; in particular the minimum over `C` is attained.

**Formalization Note.** The quantifier order is `∀ i, ∃ f`, as in the proof ("Suppose `X₀ = i`
with probability 1 …"). The competitors `θ` range over all history-dependent randomized
procedures (`Policy M`). `hA` says all decisions are available in every state. Assumption A
is kept because the theorem states it. `M.C` plays no role; the costs are `w′`, `w″`. -/
theorem theorem_3 {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a) :
    ∀ i : S, ∃ f : StationaryPolicy M, ∀ θ : Policy M,
      ratioCost f.toPolicy i w' w'' ≤ ratioCost θ i w' w'' := by sorry

end DermanSeqDecisions.Ratio
