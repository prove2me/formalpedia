-- Prove2me | Theorems.Thm_Erdos195_SignedDigitResearch_signed_binary_pattern_obstruction
-- name    : Erdos195.SignedDigitResearch.signed_binary_pattern_obstruction
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T07:59:09.028796+00:00
-- url     : https://prove2.me/theorems/2f4c4f71-f681-43ce-b5e3-0a5fc4c8ac2a
-- title:
--   Two dyadic order patterns obstruct signed-binary transport to a 4AP-free integer permutation
-- statement:
--   Let p be a permutation of the natural numbers. Suppose that for every k≥0 the values 3·2^k,2·2^k,5·2^k,4·2^k occur in that order under p, and the values 1·2^k,2·2^k,15·2^k,8·2^k also occur in that order. For any fixed choice of signs on binary place values, every bijection f from the natural numbers onto the integers satisfying f(i)=signedValue(ε,p(i)) contains a monotone four-term arithmetic progression. The signed value is the finite binary digit sum with coefficients +2^j or −2^j according to ε(j), defined by the exact terminating binary recursion. This is a construction-family obstruction; the original Erdős195 existence question remains open.
-- source:
--   Independent signed-binary transport obstruction developed in this research branch. The actual Ho permutation from arXiv:2609.12780v1 is a separately kernel-checked application: it satisfies both patterns, and even-order self-similarity propagates them to every dyadic scale. Neither this obstruction nor self-similarity is attributed to the paper. Exact actual Ho closure provenance: accepted submission ba0ba110-74af-4501-8488-3247e332dec2, MIT-licensed upstream boonsuan/4ap.

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_SignedBinary_Model

namespace Erdos195.SignedDigitResearch

theorem signed_binary_pattern_obstruction (p : ℕ ≃ ℕ) (ε : ℕ → Bool) (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = signedValue ε (p i))
    (hA : ∀ k, p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*5) ∧ p.symm (2^k*5) < p.symm (2^k*4))
    (hB : ∀ k, p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*15) ∧ p.symm (2^k*15) < p.symm (2^k*8)) :
    HasMonotoneAP f 4 := by sorry

end Erdos195.SignedDigitResearch
