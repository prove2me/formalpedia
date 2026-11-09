-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_10
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:29.676179+00:00
-- url     : https://prove2.me/theorems/b72dfee2-74d8-41d7-98d6-f5eb54387d14
-- title:
--   Claim 4.10 — certification and progress
-- statement:
--   Fix a center $c$, a level $j\le j_C$ and a client at site $v$. Then
--   $$0\le\xi_v^{(j)}\le 2\,d(c,v).$$
--   Moreover, almost surely (precisely: whenever $U_v^{(j)}>0$), for the pre-client open set $F_v$:
--   1. $(v,j)$ is certified $\iff$ $Z_v^{(j)}<\infty$ and $\xi_v^{(j)}+f_jU_v^{(j)}\le q_j(F_v)$; (4.10)
--   2. $(v,j)$ is regularly certified $\iff$ $Z_v^{(j)}<\infty$ and $\xi_v^{(j)}+f_jU_v^{(j)}\le\min\{f_j,q_j(F_v)\}$;
--   3. $q_j(F_v^+)\le\xi_v^{(j)}$ whenever $(v,j)$ is certified. (4.11)
--
--   These translate certification into a shifted-key test against the excess distance $q_j$, and show that a certification brings the excess down to $\xi_v^{(j)}$; both are used in the record arguments of Claims 4.11 and 4.12.
--
--   Differences from the source:
--   - generalization: the open set F_v of the execution, almost surely → every finite open set F and every lottery vector with U^(j) > 0; reason: U^(j) > 0 has probability one; F_v is one such set
--   - generalization: v in C, c the center of C → any site c and any client site x; reason: the claim involves only c, v and the level
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: q_j(F) = [d(c,F) − d(c,M_j)]_+ with q_j(∅) = ∞; comparisons of reals with q_j → truncated subtraction in [0, ∞]; the real ξ + f_j U compared through ENNReal.ofReal; reason: truncated subtraction is the positive part; ξ + f_j U > 0 here, so ofReal loses nothing
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.10, p. 20 (proof p. 21), eqs. (4.10)–(4.11)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.10 (Certification and progress, p. 20). For a level `j ≤ j_C` (`f_j ≤ f̂(c)`) and a
client at site `x`: `0 ≤ ξ_v^{(j)} ≤ 2 d(c, v)`. Moreover, whenever `U_v^{(j)} > 0` (almost
surely), for every pre-client open set `F`:
(4.10) `(v, j)` is certified iff `Z_v^{(j)} < ∞` and `ξ_v^{(j)} + f_j U_v^{(j)} ≤ q_j(F)`;
the regular variant with `min {f_j, q_j(F)}`; and
(4.11) `q_j(F_v^+) ≤ ξ_v^{(j)}` whenever `(v, j)` is certified. -/
theorem claim_4_10 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (c x : S) (t : Lev f) (ht : (t : ℝ) ≤ fhat f c) :
    (0 ≤ xi f c x t ∧ xi f c x t ≤ 2 * dist c x) ∧
      ∀ (F : Finset S) (u : Lev f → ℝ), 0 < u t →
        (certStep f c F x u t ↔
            key f c x u t < ⊤ ∧
              ENNReal.ofReal (xi f c x t + (t : ℝ) * u t) ≤ qexc f c t F) ∧
          (regCertStep f c F x u t ↔
            key f c x u t < ⊤ ∧
              ENNReal.ofReal (xi f c x t + (t : ℝ) * u t) ≤
                min (ENNReal.ofReal (t : ℝ)) (qexc f c t F)) ∧
          (certStep f c F x u t →
            qexc f c t (Fplus tb f F x u) ≤ ENNReal.ofReal (xi f c x t)) := by sorry

end BatchedFacilityLocation.Nonuniform
