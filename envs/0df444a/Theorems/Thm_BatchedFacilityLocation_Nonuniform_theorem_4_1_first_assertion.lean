-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_theorem_4_1_first_assertion
-- name    : BatchedFacilityLocation.Nonuniform.theorem_4_1_first_assertion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:38.638194+00:00
-- url     : https://prove2.me/theorems/8a4a9cdc-5057-4f72-8fb7-0b4f9afcdcb4
-- title:
--   Theorem 4.1, first assertion (proof, p. 24) — the single-copy bound
-- statement:
--   For every valid instance with $n$ clients in $B$ batches and every comparison solution $a$, the single-copy marginal Meyerson algorithm satisfies
--   $$\mathbb E[\mathrm{ALG}]\;\le\;130\,\mathrm{conn}(a)+48\min\Big\{H_B,\;8\max\big\{1,\sqrt{\log(n+1)}\big\}\Big\}\,\mathrm{open}(a).$$
--
--   With $B=1$ this is a constant-competitive bound for one shuffled batch, which the singleton copy of the combined algorithm uses; in general it is the batched bound fed into Observation 2.2.
--
--   Differences from the source:
--   - generalization: OPT_conn and OPT_open of the optimal clusters → conn(a) and open(a) of every comparison solution a; reason: the proof sums the cluster bound over the clusters of the solution and uses nothing about optimality
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: log → natural logarithm Real.log; reason: as in Claim 4.12
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), proof of Theorem 4.1, p. 24 (unnumbered display, "which proves the first assertion")

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Theorem 4.1, first assertion (proof, p. 24). The single-copy algorithm satisfies, against
every comparison solution `a`,
`E[ALG] ≤ 130 conn(a) + 48 min {H_B, 8 max {1, √(log (n + 1))}} open(a)`. -/
theorem theorem_4_1_first_assertion {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S)
    (f : S → ℝ) (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (a : Fin I.n → S) :
    Ex f I (ALG tb f I) ≤
      ENNReal.ofReal (130 * connCost I.loc a +
        48 * min ((harmonic I.B : ℚ) : ℝ) (8 * max 1 (Real.sqrt (Real.log (I.n + 1)))) *
          openCost f a) := by sorry

end BatchedFacilityLocation.Nonuniform
