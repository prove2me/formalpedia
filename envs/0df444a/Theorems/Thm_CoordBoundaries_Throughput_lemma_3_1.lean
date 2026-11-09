-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_3_1
-- name    : CoordBoundaries.Throughput.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:17.815201+00:00
-- url     : https://prove2.me/theorems/ce6b2feb-b7cd-4d11-b201-9934a4cf5423
-- title:
--   Lemma 3.1 — interior fractional matching recovering the interior mass
-- statement:
--   Fix a feasible solution of the relaxation (with stored schedules and both density constraints), $\eta=1/q\le1/100$ and $K\ge1$. For every outcome of independent block sampling there is a fractional matching $f$ using only interior slots and assigning positive mass only to global jobs, such that for every global job $j$
--   $$f_j\le\frac{z_j}{D_j}\,\mathbf 1\{j\text{ is absent at both boundaries}\},$$
--   where the right-hand side is zero when $D_j=0$; the union of $f$ and the initial integral matching is a feasible fractional matching; and
--   $$\mathbb E|f|\ge(1-6\eta)Z-\frac{5K|\mathcal S|}{\eta^6}.$$
--   Here $|f|=\sum_j f_j$ and the expectation is over independent block sampling.
--
--   The per-job bound controls how much fractional interior assignment a later crossing exchange must erase (Lemma 3.2).
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - encoding: "for every outcome … there is a fractional matching f … Moreover E|f| ≥ …" → there is a choice ω ↦ f(ω) with all per-outcome properties and the expectation bound for that choice; reason: the expectation refers to the matchings chosen at the outcomes
--   - encoding: "the right-hand side is defined to be zero when D_j = 0" → an explicit if D_j = 0 then 0 else z_j/D_j; reason: makes the convention independent of Lean’s x/0 = 0
--   - generalization: a solution of the full or projected consistent relaxation → the consistency constraints are not assumed; reason: the proof uses only independent sampling from x and the density constraints; consistent solutions satisfy the hypotheses
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 15–16, Lemma 3.1

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Rounding

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 3.1** (Tong–Xu, pp. 15–16). Fix a feasible relaxation solution with the density
constraints, `η = 1/q ≤ 1/100` and `K ≥ 1`. For every outcome `ω` of independent block sampling
there is a fractional matching `f` using only interior slots and assigning positive mass only to
global jobs, with `f_j ≤ (z_j/D_j)·1{j absent at both boundaries}` for every global job (the
right-hand side being `0` when `D_j = 0`), such that the union of `f` and the initial integral
matching is a feasible fractional matching; moreover `E|f| ≥ (1 − 6η)Z − 5K|𝒮|/η⁶`. -/
theorem lemma_3_1 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K Δ q : ℕ}
    (hq : 100 ≤ q) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (s : ConfigSol I P K)
    (hD₁ : s.DenseBlocks Δ q) (hD₂ : s.DenseSuper q) :
    ∃ f : Tuple I P → Fin I.n → Slot I P → ℝ,
      (∀ ω ∈ outcomes P K,
        s.IsFracMatching ω (f ω) ∧
        (∀ j σ, f ω j σ ≠ 0 → P.IsInterior σ ∧ P.IsGlobal j) ∧
        (∀ j, P.IsGlobal j →
          ∑ σ, f ω j σ ≤ (if s.Dabs j = 0 then 0 else s.z j / s.Dabs j) *
            (if P.AbsentBoth ω j then 1 else 0)) ∧
        s.IsFracMatching ω (fun j σ => f ω j σ + initFrac P ω j σ)) ∧
      (1 - 6 * eta q) * s.Z - 5 * (K : ℝ) * P.numSuper / eta q ^ 6 ≤
        s.Eprod (fun ω => ∑ j, ∑ σ, f ω j σ) := by sorry

end CoordBoundaries.Throughput
