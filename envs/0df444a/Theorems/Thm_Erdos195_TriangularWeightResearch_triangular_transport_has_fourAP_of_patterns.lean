-- Prove2me | Theorems.Thm_Erdos195_TriangularWeightResearch_triangular_transport_has_fourAP_of_patterns
-- name    : Erdos195.TriangularWeightResearch.triangular_transport_has_fourAP_of_patterns
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T08:40:22.329783+00:00
-- url     : https://prove2.me/theorems/1f121ed8-0503-43b5-aefa-7fd7f04746ad
-- title:
--   A dyadic order pattern obstructs every triangular binary-weight transport to a 4AP-free integer permutation
-- statement:
--   Let $p:\mathbb N\simeq\mathbb N$ be a permutation, and write $\operatorname{pos}(m)=p^{-1}(m)$. Assume that for every $k\ge0$ and every $n\ge2$,
--
--   $$
--   \operatorname{pos}(3\cdot2^k)<\operatorname{pos}(2\cdot2^k)
--   <\operatorname{pos}((2n+1)\cdot2^k)<\operatorname{pos}(2n\cdot2^k).
--   $$
--
--   For an arbitrary sequence of integers $a=(a_j)_{j\ge0}$, define the binary-weight map by the exact terminating recursion
--
--   $$
--   G_a(0)=0,\qquad G_a(2n)=2G_{\sigma a}(n),\qquad
--   G_a(2n+1)=2G_{\sigma a}(n)+a_0,
--   \quad (\sigma a)_j=a_{j+1}.
--   $$
--
--   If $f:\mathbb N\simeq\mathbb Z$ satisfies $f(i)=G_a(p(i))$ for every $i$, then $f$ contains a monotone four-term arithmetic progression. There are no sign, oddness, magnitude, periodicity, or growth assumptions on $a$.
--
--   The actual explicit Ho permutation is a separately checked instance of the order hypothesis. For that permutation the result rules out every triangular binary-weight transport, extending the fixed signed-digit coefficient family. The generic order hypotheses differ from the earlier signed-digit obstruction. This is a construction-family obstruction; the original Erdős195 existence question remains open.
-- source:
--   Independent triangular binary-weight obstruction developed in this research branch. The actual Ho permutation from arXiv:2609.12780v1 is a separately kernel-checked application: its first four entries, even-order self-similarity, and paired-odd precedence prove the all-scale pattern. Neither the new obstruction nor these new algorithm-specific helpers is attributed to the paper. Exact actual Ho closure provenance: accepted submission ba0ba110-74af-4501-8488-3247e332dec2, MIT-licensed upstream boonsuan/4ap.

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_TriangularBinary_Model

namespace Erdos195.TriangularWeightResearch

theorem triangular_transport_has_fourAP_of_patterns
    (p : ℕ ≃ ℕ) (a : ℕ → ℤ) (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = weightValue a (p i))
    (horder : ∀ k n : ℕ, 2 ≤ n →
      p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*(2*n+1)) ∧
      p.symm (2^k*(2*n+1)) < p.symm (2^k*(2*n))) :
    HasMonotoneAP f 4 := by sorry

end Erdos195.TriangularWeightResearch
