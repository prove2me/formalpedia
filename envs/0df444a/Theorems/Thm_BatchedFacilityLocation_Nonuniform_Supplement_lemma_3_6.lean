-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_Supplement_lemma_3_6
-- name    : BatchedFacilityLocation.Nonuniform.Supplement.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:47:07.314916+00:00
-- url     : https://prove2.me/theorems/be79ceb3-a232-4167-b101-5a6f85cf4db8
-- title:
--   Lemma 3.6 — progress and records
-- statement:
--   Let $(S,d)$ be a finite metric space of sites, all with opening cost $f>0$, and consider a batched instance of $n$ clients (client $v$ at a site of $S$) in $1\le B\le n$ nonempty batches. Meyerson's algorithm is run as a single copy on all clients in batched random order, with i.i.d. lotteries $U_v\sim\mathrm{Unif}[0,1]$. Fix a center $c\in S$ and a set $C$ of clients, with $\mathrm{conn}(C)=\sum_{v\in C}d(c,v)$, and the certificates $Y_v$, $W_b$, $K_C$ of (3.1).
--
--   For every real $\rho>1$,
--
--   $$
--   \mathbb E[K_C]\le 3+\frac{\log n}{\log\rho}+\log\Big(1+\frac{(\rho-1)\,\mathrm{conn}(C)}{f}\Big),
--   $$
--
--   where $n$ is the total number of clients and $\log$ is the natural logarithm.
--
--   Choosing $\rho$ suitably gives the $\sqrt{\log n}$ alternative to Lemma 3.5 in Theorem 3.1.
--
--   Differences from the source:
--   - generalization: Stated for a comparison cluster C of a fixed optimal solution, served by its facility c → every center c ∈ S and every set C of clients; reason: the proof uses only the center c and membership in C, never optimality; each comparison cluster is an instance
--   - encoding: the algorithm of §3 (Meyerson's rule run on the clients in batched random order) → the single-copy execution runIU on the instance: batch order σ uniform on B! permutations, in-batch shuffle induced by a uniform τ on n! permutations, lotteries i.i.d. Unif[0,1], all independent; reason: the restrictions of a uniform τ to the batches are independent uniform in-batch orders independent of σ, which is the paper's arrival law (p. 7, p. 9)
--   - encoding: U_v ~ Unif(0,1) → U_v uniform on [0,1] (published unif01), expectations as lower integrals in [0,∞]; reason: the endpoints have probability zero; the costs are nonnegative so ∫⁻ is the expectation (no integrability default)
--   - encoding: a metric space containing the clients and the comparison facilities → a finite metric space S (Fintype); reason: the algorithm opens only at client locations, so every instance and comparison solution live on the finite submetric of client locations and comparison facilities, with identical costs and distances
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: the ratio log n / log ρ is base-free, and the last term comes from E[H_N] ≤ 1 + log(1 + E[N]) on p. 13, which holds for the natural logarithm
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Lemma 3.6, p. 12 (proof p. 12–13)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_Uniform

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

/-- Lemma 3.6 (Progress and records, p. 12). Uniform opening cost `f > 0`, single-copy
execution on a valid instance with `n` clients. For every `ρ > 1`, every center `c` and every
client set `C`, `E[K_C] ≤ 3 + log n / log ρ + log (1 + (ρ - 1) conn(C) / f)` (natural log). -/
theorem lemma_3_6 {S : Type*} [Fintype S] [MetricSpace S] (f : ℝ) (hf : 0 < f)
    (I : Instance S) (hI : I.Valid) (c : S) (C : Finset (Fin I.n)) (ρ : ℝ) (hρ : 1 < ρ) :
    ExU I (KCU f I c C) ≤
      ENNReal.ofReal (3 + Real.log I.n / Real.log ρ +
        Real.log (1 + (ρ - 1) * connC I.loc c C / f)) := by sorry

end BatchedFacilityLocation.Nonuniform.Supplement
