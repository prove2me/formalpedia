-- Prove2me | Theorems.Thm_AFIsingKS_cm_contiguity
-- name    : AFIsingKS.cm_contiguity
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:43.119064+00:00
-- url     : https://prove2.me/theorems/086eccb6-d29d-46c8-a4a2-143e598fa6b8
-- title:
--   Section 2.2, p.9 — events of probability $1-o_n(1)$ transfer from the configuration model (contiguity)
-- statement:
--   Let $d\ge3$ and let $(P_n)$ be properties of simple graphs on $n$ labelled vertices. If, for the uniformly random perfect matching $M$ of $dn$ sockets,
--   $$\Pr\big(M\text{ is not simple, or }P_n\text{ holds for the contraction of }M\big)\to1,$$
--   then $P_n$ holds with probability $1-o_n(1)$ under the uniformly random $d$-regular simple graph, with $n\to\infty$ along the integers with $dn$ even.
--
--   Together with the preceding results this is the bridge from Theorem 3.1 to Theorem 1.2.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: events occurring with probability 1 − o_n(1) in the configuration model → the event is written `IsSimpleM M → P n (toGraph M)` for a family P of properties of simple graphs; reason: P is only meaningful on simple outcomes; any configuration-model event that restricts to P on them implies this hypothesis
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_AFIsingKS_toGraph

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Section 2.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.9): events of probability `1 − o_n(1)` in the configuration model also have probability
`1 − o_n(1)` under a uniformly random `d`-regular simple graph (contiguity).

**Formalization Note.** A family of graph properties `P` needs to hold under the configuration model only on the
event that the contraction is simple. The hypothesis is implied by the statement that `P` holds with high probability
on the multigraph, whatever `P` means for non-simple outcomes. -/
theorem cm_contiguity (d : ℕ) (hd : 3 ≤ d) (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    (hP : Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M → P n (toGraph M)))
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1)) :
    PottsRapidMixing.WithHighProb d P := by sorry

end AFIsingKS
