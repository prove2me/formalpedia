-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_3
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:07.498081+00:00
-- url     : https://prove2.me/theorems/89fcde52-0647-495e-939c-f74133b64257
-- title:
--   Claim 4.3 — expected step cost is at most twice the lottery charges
-- statement:
--   Fix a client at site $v$ and condition on its history $H_v$, so that the pre-client open set $F_v$ is fixed and the lotteries $U_v^{(1)},\dots,U_v^{(m)}$ are fresh i.i.d. uniform on $[0,1]$. With $p_v^{(j)}$ the lottery probabilities of (4.1),
--   $$\mathbb E[\mathrm{cost}(v)\mid H_v]\;\le\;\sum_{j=1}^m f_jp_v^{(j)}+\mathbb E[d(v,F_v^+)\mid H_v]\;\le\;2\sum_{j=1}^m f_jp_v^{(j)}.$$
--   Both inequalities are asserted.
--
--   This bounds the cost of processing one client by its expected lottery charges, the first step of Lemma 4.2.
--
--   Differences from the source:
--   - generalization: conditional expectation given the history H_v (which fixes F_v and v; U_v fresh) → integral over a fresh lottery vector, for every finite open set F and every client site x; reason: F_v is determined by H_v and U_v is independent of H_v and uniform; the source's statement is the case F = F_v
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
--   - encoding: independent Unif(0,1) lotteries → product of Lebesgue measure restricted to [0,1]; reason: the endpoints have measure zero, so the laws agree
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.3, p. 15, eq. (4.5)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.3 (p. 15). Fix a client (at site `x`) and condition on its history, i.e. fix the
pre-client open set `F = F_v`; its lotteries are fresh. Then
`E[cost(v) | H_v] ≤ Σ_j f_j p_v^{(j)} + E[d(v, F_v^+) | H_v] ≤ 2 Σ_j f_j p_v^{(j)}`. -/
theorem claim_4_3 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (F : Finset S) (x : S) :
    (∫⁻ u, stepCost tb f F x u ∂(stepLaw f) ≤
        (∑ t : Lev f, ENNReal.ofReal (t : ℝ) * pLottery f F x t) +
          ∫⁻ u, dset x (Fplus tb f F x u) ∂(stepLaw f)) ∧
      ((∑ t : Lev f, ENNReal.ofReal (t : ℝ) * pLottery f F x t) +
          ∫⁻ u, dset x (Fplus tb f F x u) ∂(stepLaw f) ≤
        2 * ∑ t : Lev f, ENNReal.ofReal (t : ℝ) * pLottery f F x t) := by sorry

end BatchedFacilityLocation.Nonuniform
