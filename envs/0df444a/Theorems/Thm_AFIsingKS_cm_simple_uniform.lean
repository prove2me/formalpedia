-- Prove2me | Theorems.Thm_AFIsingKS_cm_simple_uniform
-- name    : AFIsingKS.cm_simple_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:15.805782+00:00
-- url     : https://prove2.me/theorems/12f2efa8-5316-4f49-b36b-0aa7c8998b74
-- title:
--   Section 2.2, p.9 — the configuration model conditioned on simple is uniform
-- statement:
--   Let $M$ be a perfect matching of the $dn$ sockets. If its contraction is simple, the contracted graph is $d$-regular. Moreover, every simple $d$-regular graph $G$ on $n$ labelled vertices is the contraction of exactly $(d!)^n$ matchings:
--   $$|\{M:M\text{ simple},\ \mathrm{contraction}(M)=G\}|=(d!)^n.$$
--   Consequently, conditioned on being simple, $G\sim\mathbb G(n,d)$ is uniformly distributed over the $n$-vertex $d$-regular simple graphs. This identity transfers statements from the configuration model to the uniform random regular graph.
--
--   Differences from the source:
--   - generalization: conditioned on the event that G is simple, G is uniformly distributed → each d-regular graph has exactly (d!)^n simple matchings contracting to it, and simple matchings contract to d-regular graphs; reason: the common count is the uniformity, and the explicit value only adds to it
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_AFIsingKS_toGraph

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Section 2.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.9): "Conditioned on the event that G is simple, G is uniformly distributed over n-vertex
d-regular simple graphs."

**Formalization Note.** The contraction of a simple matching is `d`-regular, and every `d`-regular graph on `Fin n`
has the same number `(d!)^n` of simple matchings contracting to it, which is the uniformity. -/
theorem cm_simple_uniform (n d : ℕ) :
    (∀ M : Matching n d, IsSimpleM M → (toGraph M).IsRegularOfDegree d) ∧
    ∀ G ∈ PottsRapidMixing.regularGraphs n d,
      (Finset.univ.filter (fun M : Matching n d => IsSimpleM M ∧ toGraph M = G)).card =
        d.factorial ^ n := by sorry

end AFIsingKS
