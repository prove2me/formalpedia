-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_Supplement_lemma_3_5
-- name    : BatchedFacilityLocation.Nonuniform.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:46:33.092569+00:00
-- url     : https://prove2.me/theorems/ffda3b0a-dbcb-4089-b4bc-88b71396d77b
-- title:
--   Lemma 3.5 — record bound $\mathbb E[K_C]\le H_B$
-- statement:
--   Let $(S,d)$ be a finite metric space of sites, all with opening cost $f>0$, and consider a batched instance of $n$ clients (client $v$ at a site of $S$) in $1\le B\le n$ nonempty batches. Meyerson's algorithm is run as a single copy on all clients in batched random order, with i.i.d. lotteries $U_v\sim\mathrm{Unif}[0,1]$. Fix a center $c\in S$ and a set $C$ of clients, with $\mathrm{conn}(C)=\sum_{v\in C}d(c,v)$, and the certificates $Y_v$, $W_b$, $K_C$ of (3.1).
--
--   Then
--
--   $$
--   \mathbb E[K_C]\le H_B=\sum_{i=1}^{B}\frac1i .
--   $$
--
--   The certified batches are lower records of the batch keys, which gives the logarithmic dependence on the number of batches.
--
--   Differences from the source:
--   - generalization: For every comparison cluster C of a fixed optimal solution, served by its facility c → every center c ∈ S and every set C of clients; reason: the proof uses only the center c and membership in C, never optimality; each comparison cluster is an instance
--   - encoding: the algorithm of §3 (Meyerson's rule run on the clients in batched random order) → the single-copy execution runIU on the instance: batch order σ uniform on B! permutations, in-batch shuffle induced by a uniform τ on n! permutations, lotteries i.i.d. Unif[0,1], all independent; reason: the restrictions of a uniform τ to the batches are independent uniform in-batch orders independent of σ, which is the paper's arrival law (p. 7, p. 9)
--   - encoding: U_v ~ Unif(0,1) → U_v uniform on [0,1] (published unif01), expectations as lower integrals in [0,∞]; reason: the endpoints have probability zero; the costs are nonnegative so ∫⁻ is the expectation (no integrability default)
--   - encoding: a metric space containing the clients and the comparison facilities → a finite metric space S (Fintype); reason: the algorithm opens only at client locations, so every instance and comparison solution live on the finite submetric of client locations and comparison facilities, with identical costs and distances
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Lemma 3.5, p. 11 (proof p. 11–12)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_Uniform

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

/-- Lemma 3.5 (Record bound, p. 11). Uniform opening cost `f > 0`, single-copy execution on a
valid instance with `B` batches. For every center `c` and client set `C`,
`E[K_C] ≤ H_B = Σ_{i=1}^{B} 1/i`. -/
theorem lemma_3_5 {S : Type*} [Fintype S] [MetricSpace S] (f : ℝ) (hf : 0 < f)
    (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n)) :
    ExU I (KCU f I c C) ≤ ENNReal.ofReal ((harmonic I.B : ℚ) : ℝ) := by sorry

end BatchedFacilityLocation.Nonuniform.Supplement
