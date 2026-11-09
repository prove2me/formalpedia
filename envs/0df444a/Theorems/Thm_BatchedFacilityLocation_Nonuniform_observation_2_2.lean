-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_observation_2_2
-- name    : BatchedFacilityLocation.Nonuniform.observation_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:01.37703+00:00
-- url     : https://prove2.me/theorems/469d11c7-e576-48f0-9166-72022473fd17
-- title:
--   Observation 2.2 — singleton–nonsingleton transfer
-- statement:
--   Fix the sites and opening costs. Let $A_{BR}$ be a batched random-order algorithm such that, for all $k,m$, on every instance with at most $k$ batches and at most $m$ clients and against every comparison solution $a$,
--   $$\mathbb E[\mathrm{ALG}]\le\alpha\,\mathrm{conn}(a)+\mathrm{CR}_{BR}(k,m)\,\mathrm{open}(a),$$
--   and let $A_{RO}$ be an ordinary random-order algorithm with competitive ratio $\mathrm{CR}_{RO}$: $\mathbb E[\mathrm{ALG}]\le\mathrm{CR}_{RO}\,\mathrm{OPT}$ on every instance whose batches are all singletons. Then on every instance with $n$ clients in $B$ batches and against every comparison solution $a$, the combined algorithm satisfies
--   $$\mathbb E[\mathrm{ALG}_{\mathrm{comb}}]\le\max\{\alpha,\mathrm{CR}_{RO}\}\,\mathrm{conn}(a)+\big(\mathrm{CR}_{RO}+\mathrm{CR}_{BR}(B,2(n-B))\big)\,\mathrm{open}(a).$$
--
--   It sharpens a dependence on the number of clients $n$ into one on $n-B$: the nonsingleton batches contain at most $2(n-B)$ clients.
--
--   Differences from the source:
--   - generalization: a batched random-order algorithm and an ordinary random-order algorithm → any functions A : List (List S) → [0, ∞] giving the expected cost for each batch arrival sequence; reason: the observation uses only expectations of the two copies; every algorithm defines such a function
--   - generalization: CR_BR(m) nondecreasing, bound on instances with at most m clients; conclusion with CR_BR(2(n − B)) → CR_BR(k, m), bound on instances with at most k batches and at most m clients, no monotonicity; conclusion with CR_BR(B, 2(n − B)); reason: CR_BR(k, m) := CR_BR(m) recovers the source; the batch argument carries the H_B dependence used on p. 24
--   - generalization: conclusion against OPT_conn and OPT_open → against every comparison solution a; reason: the proof restricts a fixed comparison solution to the two copies; an optimal one is a special case
--   - generalization: ALG_comb opens the union of both copies' facilities and connects each client to the closest → ALG_comb is the sum of the two copies' costs; reason: the union version costs at most the sum (proof of Obs. 2.2), so bounding the sum is stronger
--   - reading: a is a constant; competitive ratios → α, CR_RO and CR_BR(k, m) are nonnegative reals (NNReal); reason: §2 defines competitive ratios with α ≥ 1; a negative CR_BR(B, 0) would make the case n = B false
--   - encoding: a copy without clients → costs 0 (it is not run); reason: a copy with no clients opens nothing
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Observation 2.2, p. 8

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Batched

open MeasureTheory
open scoped ENNReal NNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Observation 2.2 (Singleton–nonsingleton transfer, p. 8). Let `A_BR` be a batched
random-order algorithm with `E[ALG] ≤ a·conn + CR_BR(k, m)·open` against every comparison
solution on every instance with at most `k` batches and at most `m` clients, and let `A_RO` be
an ordinary random-order algorithm (all batches singletons) with `E[ALG] ≤ CR_RO·OPT`. Then the
combined algorithm satisfies, against every comparison solution,
`E[ALG_comb] ≤ max {a, CR_RO} conn + (CR_RO + CR_BR(B, 2(n - B))) open`. -/
theorem observation_2_2 {S : Type*} [Fintype S] [MetricSpace S] (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (A_RO A_BR : List (List S) → ℝ≥0∞) (α CR_RO : ℝ≥0)
    (CR_BR : ℕ → ℕ → ℝ≥0)
    (hBR : ∀ k m : ℕ, ∀ J : Instance S, J.Valid → J.B ≤ k → J.n ≤ m → ∀ a : Fin J.n → S,
      brExp A_BR J ≤
        (α : ℝ≥0∞) * ENNReal.ofReal (connCost J.loc a) +
          (CR_BR k m : ℝ≥0∞) * ENNReal.ofReal (openCost f a))
    (hRO : ∀ n' : ℕ, 1 ≤ n' → ∀ loc : Fin n' → S,
      brExp A_RO (roInstance loc) ≤ (CR_RO : ℝ≥0∞) * OPT f loc)
    (I : Instance S) (hI : I.Valid) (a : Fin I.n → S) :
    brExp (combine A_RO A_BR) I ≤
      ((max α CR_RO : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (connCost I.loc a) +
        ((CR_RO : ℝ≥0∞) + (CR_BR I.B (2 * (I.n - I.B)) : ℝ≥0∞)) *
          ENNReal.ofReal (openCost f a) := by sorry

end BatchedFacilityLocation.Nonuniform
