-- Prove2me | Theorems.Thm_Erdos30_singer_construction
-- name    : Erdos30.singer_construction
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:42:10.680993+00:00
-- url     : https://prove2.me/theorems/1155a2d1-fd96-4912-b588-b1205ed0aa67
-- title:
--   Singer's construction: $h(q^2+q+1)\ge q+1$ for prime powers $q$
-- statement:
--   Let $q$ be a prime power. Then $\{1,2,\dots,q^2+q+1\}$ contains a Sidon set with $q+1$ elements; equivalently,
--
--   $$h(q^2+q+1)\ \ge\ q+1.$$
--
--   This is the integer consequence of Singer's theorem: there is a set of $q+1$ residues modulo $m=q^2+q+1$ whose nonzero differences represent every nonzero residue exactly once (a perfect difference set). Distinct differences modulo $m$ imply distinct differences in $\mathbb Z$, so the representatives in $\{1,\dots,m\}$ form a Sidon set. It is the source of all good lower bounds for $h(N)$.
-- source:
--   J. Singer, A theorem in finite projective geometry and some applications to number theory, Trans. Amer. Math. Soc. 43 (1938), 377–385, https://doi.org/10.1090/S0002-9947-1938-1501951-4 (main theorem: perfect difference sets of size q+1 modulo q^2+q+1 for prime powers q); cited at Erdős Problem #30, https://www.erdosproblems.com/30 as [Si38]

import Mathlib
import Definitions.Def_Erdos30Basic

namespace Erdos30

theorem singer_construction (q : ℕ) (hq : IsPrimePow q) :
    q + 1 ≤ h (q ^ 2 + q + 1) := by
  sorry

end Erdos30
