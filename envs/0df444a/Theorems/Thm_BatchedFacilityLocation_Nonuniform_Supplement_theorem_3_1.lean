-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_Supplement_theorem_3_1
-- name    : BatchedFacilityLocation.Nonuniform.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:47:30.499865+00:00
-- url     : https://prove2.me/theorems/22b25b3d-4f87-49b5-987d-952473403821
-- title:
--   Theorem 3.1 — uniform opening costs: $O(\min\{\log(B+1),\sqrt{\log(n-B+2)}\})$-competitive
-- statement:
--   There are absolute constants $C_1,C_2>0$ with the following property. Let $(S,d)$ be a finite metric space of sites, all with the same opening cost $f>0$, and let an instance of $n\ge1$ clients (each at a site of $S$) be partitioned into $1\le B\le n$ nonempty batches that arrive in uniformly random order. Run two independent copies of Meyerson's algorithm (each batch shuffled uniformly, clients processed one at a time, facility opened at $v$ with probability $\min\{1,d(v,F_v)/f\}$): one copy on the singleton batches, one on the nonsingleton batches. Then for every comparison solution $a$ assigning each client to a site,
--
--   $$
--   \mathbb E[\mathrm{ALG}]\le C_1\,\mathrm{conn}(a)+C_2\,\min\Big\{\log(B+1),\sqrt{\log(n-B+2)}\Big\}\,\mathrm{open}(a),
--   $$
--
--   where $\mathrm{conn}(a)=\sum_v d(v,a(v))$ and $\mathrm{open}(a)=f\cdot|a(\text{clients})|$. In particular $\mathbb E[\mathrm{ALG}]\le O(1)\,\mathrm{OPT_{conn}}+O(\min\{\log(B+1),\sqrt{\log(n-B+2)}\})\,\mathrm{OPT_{open}}$.
--
--   This is the uniform-cost counterpart of the mission's goal (Theorem 4.1), for Meyerson's original rule rather than the marginal rule with rounded costs.
--
--   Differences from the source:
--   - encoding: there exists an algorithm with E[ALG] ≤ O(1) OPT_conn + O(min{…}) OPT_open → ∃ C₁ C₂ > 0, quantified before the metric, f and the instance, for the explicit two-copy algorithm meyComb of §3.1; reason: the O(·) are absolute constants (p. 13); the algorithm is the one the paper constructs, so the existential is witnessed
--   - generalization: the bound against OPT (an optimal solution's clusters) → the bound against every comparison solution a; reason: OPT is attained by some comparison solution, so the source's bound is the instance a = an optimum
--   - generalization: the combined algorithm opens the union of the copies' facilities and connects each client to the closest one → the cost of the combined algorithm is the sum of the two copies' costs (published combine); reason: the union version costs at most the sum (proof of Observation 2.2, p. 8), so the Lean bound implies the source's
--   - encoding: U_v ~ Unif(0,1) → U_v uniform on [0,1] (published unif01), expectations as lower integrals in [0,∞]; reason: the endpoints have probability zero; the costs are nonnegative so ∫⁻ is the expectation (no integrability default)
--   - encoding: a metric space containing the clients and the comparison facilities → a finite metric space S (Fintype); reason: the algorithm opens only at client locations, so every instance and comparison solution live on the finite submetric of client locations and comparison facilities, with identical costs and distances
--   - encoding: n − B → ((I.n - I.B : ℕ) : ℝ); reason: validity gives B ≤ n, so the natural-number subtraction is exact
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: a change of base only changes the constants
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Theorem 3.1, p. 9 (algorithm §3.1 p. 9, proof p. 13 via Corollary 3.4, Lemmas 3.5, 3.6 and Observation 2.2)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_Uniform

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

universe u

/-- Theorem 3.1 (Uniform opening costs, p. 9). There are absolute constants `C₁, C₂ > 0` such
that for every finite metric space of sites, every common opening cost `f > 0`, every instance
of `n ≥ 1` clients in `1 ≤ B ≤ n` nonempty batches and every comparison solution `a`, the
two-copy Meyerson algorithm satisfies
`E[ALG] ≤ C₁ conn(a) + C₂ min {log (B + 1), √(log (n - B + 2))} open(a)`. -/
theorem theorem_3_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (S : Type u) [Fintype S] [MetricSpace S] (f : ℝ), 0 < f →
        ∀ I : Instance S, I.Valid → ∀ a : Fin I.n → S,
          brExp (meyComb f) I ≤
            ENNReal.ofReal (C₁ * connCost I.loc a +
              C₂ * min (Real.log (I.B + 1)) (Real.sqrt (Real.log (((I.n - I.B : ℕ) : ℝ) + 2))) *
                openCost (fun _ => f) a) := by sorry

end BatchedFacilityLocation.Nonuniform.Supplement
