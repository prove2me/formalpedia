-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_12
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:15.980057+00:00
-- url     : https://prove2.me/theorems/522f8e2a-be2d-4ced-928e-b7e9484d48e1
-- title:
--   Claim 4.12 — bound for regular certifications
-- statement:
--   Fix a center $c$, a set of clients $C$, a level $j\le j_C$ and $\rho>1$. With $n$ the number of clients of the instance,
--   $$\mathbb E\big[L_C^{(j)}\big]\;\le\;3+\frac{\log n}{\log\rho}+\log\Big(1+\frac{(\rho-1)\sum_{v\in C}\xi_v^{(j)}}{f_j}\Big),$$
--   where $L_C^{(j)}$ counts the batches containing a regular level-$j$ certification from $C$.
--
--   This yields the progress bound (4.9) and the $\sqrt{\log n}$ term of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: a comparison cluster C with center c → any set C of clients and any site c; reason: the statement and proof use only C, c and j_C = level of f-hat(c); a cluster of a comparison solution is a special case
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
--   - encoding: log → natural logarithm Real.log; reason: the source's ratio log n / log ρ and its Jensen step use one base; the natural one is the reading of the proof
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.12, p. 21 (proof p. 22–23)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.12 (Bound for regular certifications, p. 21). For every level `j ≤ j_C` and every
`ρ > 1`: `E[L_C^{(j)}] ≤ 3 + log n / log ρ + log (1 + (ρ - 1) Σ_{v ∈ C} ξ_v^{(j)} / f_j)`. -/
theorem claim_4_12 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n))
    (t : Lev f) (ht : (t : ℝ) ≤ fhat f c) (ρ : ℝ) (hρ : 1 < ρ) :
    Ex f I (LC tb f I c C t) ≤
      ENNReal.ofReal (3 + Real.log I.n / Real.log ρ +
        Real.log (1 + (ρ - 1) * (∑ i ∈ C, xi f c (I.loc i) t) / (t : ℝ))) := by sorry

end BatchedFacilityLocation.Nonuniform
