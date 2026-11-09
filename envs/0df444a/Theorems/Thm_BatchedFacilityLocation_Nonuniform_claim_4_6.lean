-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_claim_4_6
-- name    : BatchedFacilityLocation.Nonuniform.claim_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:19:34.112194+00:00
-- url     : https://prove2.me/theorems/76ef3b47-d32c-49b7-a4f6-bfa1b610d6b6
-- title:
--   Claim 4.6 — near clients
-- statement:
--   Fix a center $c$, a set of clients $C$ and a batch $b$, and let $C_b=C\cap b$. Call *near* a set $N\subseteq C_b$ of $\lceil|C_b|/2\rceil$ clients closest to $c$: every client of $N$ is at least as close to $c$ as every client of $C_b\setminus N$ (ties broken in any fixed way). Then
--   $$\mathbb E\Big[\sum_{v\in N}Y_v\Big]\;\le\;\mathbb E[W_b]+2\,\mathrm{conn}(C_b).$$
--
--   This is the first half of Lemma 4.5: the near half of a batch pays at most one first certification per level plus its connection cost.
--
--   Differences from the source:
--   - generalization: a comparison cluster C with center c → any set C of clients and any site c; reason: the statement and proof use only C, c and j_C = level of f-hat(c); a cluster of a comparison solution is a special case
--   - generalization: the ceil(|C_b|/2) clients closest to c with a fixed tie-breaking, under the assumption C_b nonempty → any set N of that size inside C_b whose members are at least as close to c as all non-members; C_b may be empty; reason: every fixed tie-breaking gives such an N; for C_b empty N is empty and the claim is trivial
--   - generalization: a fixed distance tie-breaking rule → an arbitrary tie-breaking rule tb (any choice of a closest point); reason: the result holds for every fixed rule; the source's rule is one instance
--   - reading: permitted sites with a metric, known in advance → a finite metric space S of sites (Fintype S, MetricSpace S); reason: the algorithm needs finitely many rounded levels f_1 < ... < f_m and attained minima d(v, M_j); with infinitely many levels (4.1) is undefined
--   - encoding: uniform batch order, each batch shuffled uniformly and independently, lotteries i.i.d. Unif(0,1) independent of both orders → sigma uniform on Perm (Fin B), tau uniform on Perm (Fin n), clients processed in lexicographic order of (sigma(batch i), tau(i)); lotteries i.i.d. uniform on [0,1]; reason: tau restricted to each batch gives independent uniform in-batch orders independent of sigma; same law
--   - encoding: real-valued expectations and costs, d(v, empty set) = infinity → values in [0, infinity] (ENNReal lower integrals, ENNReal.ofReal of real costs); reason: all quantities are nonnegative; avoids the Bochner integral of a non-integrable function
--   - encoding: levels j = 1..m with rounded costs f_1 < ... < f_m; j <= j_C → a level is identified with its rounded cost t = f_j (subtype of the finite set of values of f-hat); j <= j_C is t <= f-hat(c); d_v^(j-1) = d(v, {y : f-hat(y) < f_j}); reason: the levels are exactly the distinct values of f-hat; same objects
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Claim 4.6, p. 17 (proof p. 17–18), inside the proof of Lemma 4.5

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

/-- Claim 4.6 (Near clients, p. 17). Let `C_b = C ∩ b` and let `N` be a set of `⌈|C_b|/2⌉`
clients of `C_b` closest to `c` (every client of `N` is at least as close to `c` as every
client of `C_b \ N`; any tie-breaking). Then `E[Σ_{v ∈ N} Y_v] ≤ E[W_b] + 2 conn(C_b)`. -/
theorem claim_4_6 {S : Type*} [Fintype S] [MetricSpace S] (tb : TieBreak S) (f : S → ℝ)
    (hf : ∀ y, 0 < f y) (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n))
    (b : Fin I.B) (N : Finset (Fin I.n))
    (hN : N ⊆ C.filter (fun i => I.batch i = b))
    (hcard : N.card = ((C.filter (fun i => I.batch i = b)).card + 1) / 2)
    (hnear : ∀ u ∈ N, ∀ w ∈ C.filter (fun i => I.batch i = b), w ∉ N →
      dist c (I.loc u) ≤ dist c (I.loc w)) :
    Ex f I (fun σ τ U => ∑ i ∈ N, Y tb f I c σ τ U i) ≤
      Ex f I (Wb tb f I c C b) +
        2 * ENNReal.ofReal (connC I.loc c (C.filter (fun i => I.batch i = b))) := by sorry

end BatchedFacilityLocation.Nonuniform
