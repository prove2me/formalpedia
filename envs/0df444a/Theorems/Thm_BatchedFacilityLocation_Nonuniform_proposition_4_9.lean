-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_proposition_4_9
-- name    : BatchedFacilityLocation.Nonuniform.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:37.466337+00:00
-- url     : https://prove2.me/theorems/3f166aef-bd36-4819-a9d6-22770e46318a
-- title:
--   Proposition 4.9 — bounds at each level
-- statement:
--   Fix a center $c$ with cluster $C$, a level $j\le j_C$ and $\rho>1$. Then
--   $$\mathbb E\big[K_C^{(j)}\big]\le H_B,\qquad(4.8)$$
--   $$\mathbb E\big[L_C^{(j)}\big]\le 3+\frac{\log n}{\log\rho}+\log\Big(1+\frac{2(\rho-1)\,\mathrm{conn}(C)}{f_j}\Big).\qquad(4.9)$$
--
--   Both bounds are asserted; summing over levels with geometric prices gives the two bounds on $\mathbb E[W_C]$ used in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: a comparison cluster C with center c → any set C of clients and any site c; reason: the statement and proof use only C, c and j_C = level of f-hat(c); a cluster of a comparison solution is a special case
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
--   - encoding: log → natural logarithm Real.log; reason: as in Claim 4.12
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Proposition 4.9, p. 20, eqs. (4.8)–(4.9)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Proposition 4.9 (Bounds at each level, p. 20). For every level `j ≤ j_C` and `ρ > 1`:
(4.8) `E[K_C^{(j)}] ≤ H_B` and
(4.9) `E[L_C^{(j)}] ≤ 3 + log n / log ρ + log (1 + 2 (ρ - 1) conn(C) / f_j)`. -/
theorem proposition_4_9 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n))
    (t : Lev f) (ht : (t : ℝ) ≤ fhat f c) (ρ : ℝ) (hρ : 1 < ρ) :
    Ex f I (KC tb f I c C t) ≤ ENNReal.ofReal ((harmonic I.B : ℚ) : ℝ) ∧
      Ex f I (LC tb f I c C t) ≤
        ENNReal.ofReal (3 + Real.log I.n / Real.log ρ +
          Real.log (1 + 2 * (ρ - 1) * connC I.loc c C / (t : ℝ))) := by sorry

end BatchedFacilityLocation.Nonuniform
