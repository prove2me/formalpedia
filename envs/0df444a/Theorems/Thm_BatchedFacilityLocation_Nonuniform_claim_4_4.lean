-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_4
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:45.357808+00:00
-- url     : https://prove2.me/theorems/2c13fd8d-d8bb-4626-8e87-b6f87a07657f
-- title:
--   Claim 4.4 — lottery charges are at most certified charges plus 3d(c, v)
-- statement:
--   Fix a client at site $v$, a center $c$, and condition on the history $H_v$ (so $F_v$ is fixed and the lotteries of $v$ are fresh). Then
--   $$\sum_{j=1}^m f_jp_v^{(j)}\;\le\;\mathbb E[Y_v\mid H_v]+3\,d(c,v),$$
--   where $Y_v=\sum_{j\le j_C}f_j\mathbf 1\{(v,j)\text{ certified}\}$.
--
--   Together with Claim 4.3 this gives $\mathbb E[\mathrm{cost}(v)\mid H_v]\le 6d(c,v)+2\mathbb E[Y_v\mid H_v]$.
--
--   Differences from the source:
--   - generalization: conditional expectation given the history H_v (which fixes F_v and v; U_v fresh) → integral over a fresh lottery vector, for every finite open set F and every client site x; reason: F_v is determined by H_v and U_v is independent of H_v and uniform; the source's statement is the case F = F_v
--   - generalization: v in C and c the center of C → any site c and any client site x; reason: the proof uses only c in M_{j_C}, which holds for every c
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
--   - encoding: independent Unif(0,1) lotteries → product of Lebesgue measure restricted to [0,1]; reason: the endpoints have measure zero, so the laws agree
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.4, p. 16

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.4 (p. 16). Fix a client (at site `x`), a center `c`, and condition on the history
(fix `F = F_v`). Then `Σ_j f_j p_v^{(j)} ≤ E[Y_v | H_v] + 3 d(c, v)`. -/
theorem claim_4_4 {S : Type*} [Fintype S] [MetricSpace S] (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (c : S) (F : Finset S) (x : S) :
    ∑ t : Lev f, ENNReal.ofReal (t : ℝ) * pLottery f F x t ≤
      ∫⁻ u, Ystep f c F x u ∂(stepLaw f) + 3 * ENNReal.ofReal (dist c x) := by sorry

end BatchedFacilityLocation.Nonuniform
