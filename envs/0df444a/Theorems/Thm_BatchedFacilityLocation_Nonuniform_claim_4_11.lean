-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_11
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:43.709551+00:00
-- url     : https://prove2.me/theorems/781ad889-be87-491d-862f-001335cb5387
-- title:
--   Claim 4.11 — record bound
-- statement:
--   Fix a center $c$, a set of clients $C$ and a level $j\le j_C$. Then
--   $$\mathbb E\big[K_C^{(j)}\big]\;\le\;H_B,$$
--   where $K_C^{(j)}$ counts the batches containing a level-$j$ certification from $C$ and $H_B=\sum_{i=1}^B1/i$.
--
--   This is the harmonic bound (4.8); it gives the $\log(B+1)$ term of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: a comparison cluster C with center c → any set C of clients and any site c; reason: the statement and proof use only C, c and j_C = level of f-hat(c); a cluster of a comparison solution is a special case
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.11, p. 21

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.11 (Record bound, p. 21). For every level `j ≤ j_C`: `E[K_C^{(j)}] ≤ H_B`. -/
theorem claim_4_11 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n))
    (t : Lev f) (ht : (t : ℝ) ≤ fhat f c) :
    Ex f I (KC tb f I c C t) ≤ ENNReal.ofReal ((harmonic I.B : ℚ) : ℝ) := by sorry

end BatchedFacilityLocation.Nonuniform
