-- Prove2me | Theorems.Thm_AKS_lcm_lower
-- name    : AKS.lcm_lower
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:51:09.889273+00:00
-- url     : https://prove2.me/theorems/ac6e08ab-6c71-464f-93f8-cce29c49b8be
-- title:
--   The lcm of the first m numbers is at least 2^m (Lemma 3.1)
-- statement:
--   Lemma 3.1 of the paper: for m at least 7, the least common multiple of the numbers 1 through m is at least 2^m. This is the classical Chebyshev-type bound of Nair that the paper cites, and it is the counting ingredient of Lemma 4.3: it guarantees that the least common multiple of the window of candidate r's outruns the product that all the bad candidates divide, so that at least one candidate in the window has a large order of n.
--
--   **Formalization Note** The lcm is the definition lcmFirst m, the fold of Nat.lcm over the list of the first m numbers.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 3 (Lemma 3.1, after Nair 1982).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Lemma 3.1 of the paper: the lcm of the first m numbers is at least 2^m.  -/
theorem lcm_lower (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ lcmFirst m := by sorry

end AKS
