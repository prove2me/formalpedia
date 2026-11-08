-- Prove2me | Theorems.Thm_AFIsingKS_cm_simple_prob
-- name    : AFIsingKS.cm_simple_prob
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:27.595079+00:00
-- url     : https://prove2.me/theorems/26d0714b-1d8e-40b3-86a5-41e0f00babb2
-- title:
--   Section 2.2, p.9 — the configuration model is simple with probability $\Omega_d(1)$
-- statement:
--   For every integer $d\ge3$ there are $c>0$ and $N$ such that for all $n\ge N$ with $dn$ even, the uniformly random perfect matching of $dn$ sockets contracts to a simple graph with probability at least $c$.
--
--   This is the standard lower bound that makes the transfer from the configuration model to uniform random regular graphs possible.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9, used on p.11

import Mathlib
import Definitions.Def_AFIsingKS_toGraph

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Section 2.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.9, used on p.11): the configuration model is simple with probability `Ω_d(1)`. -/
theorem cm_simple_prob (d : ℕ) (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      c ≤ cmProb (fun M : Matching n d => IsSimpleM M) := by sorry

end AFIsingKS
