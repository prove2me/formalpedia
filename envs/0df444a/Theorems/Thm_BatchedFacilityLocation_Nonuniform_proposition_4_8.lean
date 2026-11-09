-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_proposition_4_8
-- name    : BatchedFacilityLocation.Nonuniform.proposition_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:38.966706+00:00
-- url     : https://prove2.me/theorems/a810dad8-0cda-4673-a5e8-f6aa09ceaefd
-- title:
--   Proposition 4.8 — reduction to first certificates
-- statement:
--   For every cluster $C$ with center $c$,
--   $$\mathbb E[\mathrm{ALG}(C)]\;\le\;34\,\mathrm{conn}(C)+12\,\mathbb E[W_C],$$
--   where $W_C=\sum_bW_b$ charges $f_j$ once per batch and level $j\le j_C$ with a certification from $C$.
--
--   This reduces the cost of a cluster to first certificates, which §4.4 bounds level by level.
--
--   Differences from the source:
--   - generalization: a comparison cluster C with center c → any set C of clients and any site c; reason: the statement and proof use only C, c and j_C = level of f-hat(c); a cluster of a comparison solution is a special case
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Proposition 4.8, p. 20

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Proposition 4.8 (Reduction to first certificates, p. 20). For every cluster `C` with center
`c`: `E[ALG(C)] ≤ 34 conn(C) + 12 E[W_C]`. -/
theorem proposition_4_8 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n)) :
    Ex f I (ALGC tb f I C) ≤
      34 * ENNReal.ofReal (connC I.loc c C) + 12 * Ex f I (WC tb f I c C) := by sorry

end BatchedFacilityLocation.Nonuniform
