-- Prove2me | Theorems.Thm_FanInSemigroup_theorem_2_3
-- name    : FanInSemigroup.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:01.091281+00:00
-- url     : https://prove2.me/theorems/06000390-b3a7-458f-9be2-e49ae134483e
-- title:
--   Theorem 2.3 [FSS] — no constant-depth polynomial-size circuits for sum mod $k$
-- statement:
--   For every $m>1$ and every injective encoding of the sum-zero mod $m$ semigroup, that is $\{0,\dots,m-1\}$ with the product $ij=i+j \bmod m$, there are no constant depth, polynomial size circuits computing the semigroup.
--
--   This is the lower bound behind the main theorem. The case $m=2$ is the parity lower bound of Furst, Saxe and Sipser, and the paper cites the statement from them for every $m>1$.
--
--   Differences from the source:
--   - encoding: the sum-zero mod k semigroup: {0,...,k−1} with ij = i + j mod k → Multiplicative (ZMod m); reason: the same semigroup; the page's k is called m because k counts bits here
--   - reading: "computing sum zero mod k" under an unnamed encoding → every injective encoding; reason: the page's notion of computing a semigroup fixes an arbitrary encoding
--   - reading: "circuits" with no uniformity stated → a non-uniform family, one circuit per n ≥ 1, with constants independent of n; reason: the page states no uniformity condition
--   - encoding: polynomial size → size ≤ c·n^c for n ≥ 1; reason: equivalent at n ≥ 1 to any polynomial bound
--   - encoding: a directed acyclic graph with input nodes labelled by variables → gates in topological order, one input node per variable; reason: merging input nodes with the same label only lowers the size; no instance changes
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Theorem 2.3, p.54

import Definitions.Def_FanInSemigroup_HasConstDepthPolySize

set_option autoImplicit false

namespace FanInSemigroup

/-- **Theorem 2.3 [FSS].** Chandra, Fortune, Lipton, STOC 1983, p.54: "There are no polynomial
size, constant depth circuits for computing sum zero mod k, any k > 1."

**Formalization Note.** The page defines the sum-zero mod k semigroups as {0,1,...,k−1} with
operation ij = i + j mod k, which is `Multiplicative (ZMod m)`. "Computing" is in the sense of
p.54, under an arbitrary injective encoding. The paper cites this from Furst, Saxe, Sipser. -/
theorem theorem_2_3 (m : ℕ) (hm : 1 < m) {k : ℕ} (e : Multiplicative (ZMod m) → Fin k → Bool)
    (he : Function.Injective e) : ¬ HasConstDepthPolySize e := by sorry

end FanInSemigroup
