-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_7
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:20.546971+00:00
-- url     : https://prove2.me/theorems/f2fe1aee-831e-4807-85a0-6950fb80b2b8
-- title:
--   Claim 4.7 — far clients
-- statement:
--   Fix a center $c$. For two distinct clients $u\ne v$ of the same batch $b$ (co-located clients are allowed, with $d(u,v)=0$),
--   $$\mathbb E[Y_u+Y_v]\;\le\;6\,\mathbb E[Y_u]+2\,d(u,v).$$
--
--   Pairing each far client of a batch with a distinct near client, this lets Lemma 4.5 charge the far clients to the near ones.
--
--   Differences from the source:
--   - generalization: distinct u, v in C_b = C ∩ b, c the center of C → any site c and any two distinct clients u, v of the same batch; reason: Y_u and Y_v depend only on c, not on C; the source's pairs are a special case
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.7, p. 18 (proof p. 19)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.7 (Far clients, p. 18). For distinct clients `u, v` of the same batch,
`E[Y_u + Y_v] ≤ 6 E[Y_u] + 2 d(u, v)`. -/
theorem claim_4_7 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (u v : Fin I.n)
    (huv : u ≠ v) (hb : I.batch u = I.batch v) :
    Ex f I (fun σ τ U => Y tb f I c σ τ U u + Y tb f I c σ τ U v) ≤
      6 * Ex f I (fun σ τ U => Y tb f I c σ τ U u) +
        2 * ENNReal.ofReal (dist (I.loc u) (I.loc v)) := by sorry

end BatchedFacilityLocation.Nonuniform
