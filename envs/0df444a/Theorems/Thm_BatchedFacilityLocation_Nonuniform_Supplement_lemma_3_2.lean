-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_Supplement_lemma_3_2
-- name    : BatchedFacilityLocation.Nonuniform.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:44:15.456+00:00
-- url     : https://prove2.me/theorems/32540104-191b-49ba-b41e-c93a73f6bb04
-- title:
--   Lemma 3.2 — reduction to certified charges (uniform costs)
-- statement:
--   Let $(S,d)$ be a finite metric space of sites, all with opening cost $f>0$, and consider a batched instance of $n$ clients (client $v$ at a site of $S$) in $1\le B\le n$ nonempty batches. Meyerson's algorithm is run as a single copy on all clients in batched random order, with i.i.d. lotteries $U_v\sim\mathrm{Unif}[0,1]$. Fix a center $c\in S$ and a set $C$ of clients, with $\mathrm{conn}(C)=\sum_{v\in C}d(c,v)$, and the certificates $Y_v$, $W_b$, $K_C$ of (3.1).
--
--   Then
--
--   $$
--   \mathbb E[\mathrm{ALG}(C)]\le 4\,\mathrm{conn}(C)+2\,\mathbb E\Big[\sum_{v\in C}Y_v\Big].
--   $$
--
--   This reduces the algorithm's cost on a cluster to the certified openings, the first step of the analysis of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: Stated for a comparison cluster C of a fixed optimal solution, served by its facility c → every center c ∈ S and every set C of clients; reason: the proof uses only the center c and membership in C, never optimality; each comparison cluster is an instance
--   - encoding: the algorithm of §3 (Meyerson's rule run on the clients in batched random order) → the single-copy execution runIU on the instance: batch order σ uniform on B! permutations, in-batch shuffle induced by a uniform τ on n! permutations, lotteries i.i.d. Unif[0,1], all independent; reason: the restrictions of a uniform τ to the batches are independent uniform in-batch orders independent of σ, which is the paper's arrival law (p. 7, p. 9)
--   - encoding: U_v ~ Unif(0,1) → U_v uniform on [0,1] (published unif01), expectations as lower integrals in [0,∞]; reason: the endpoints have probability zero; the costs are nonnegative so ∫⁻ is the expectation (no integrability default)
--   - encoding: a metric space containing the clients and the comparison facilities → a finite metric space S (Fintype); reason: the algorithm opens only at client locations, so every instance and comparison solution live on the finite submetric of client locations and comparison facilities, with identical costs and distances
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Lemma 3.2, p. 10 (setting §3.1 p. 9)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_Uniform

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

/-- Lemma 3.2 (p. 10). Uniform opening cost `f > 0`, single-copy execution of Meyerson's
algorithm on a valid batched instance. For every center `c` and every set `C` of clients,
`E[ALG(C)] ≤ 4 conn(C) + 2 E[Σ_{v ∈ C} Y_v]`. -/
theorem lemma_3_2 {S : Type*} [Fintype S] [MetricSpace S] (f : ℝ) (hf : 0 < f)
    (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n)) :
    ExU I (ALGCU f I C) ≤
      4 * ENNReal.ofReal (connC I.loc c C) +
        2 * ExU I (fun σ τ U => ∑ i ∈ C, YU f I c σ τ U i) := by sorry

end BatchedFacilityLocation.Nonuniform.Supplement
