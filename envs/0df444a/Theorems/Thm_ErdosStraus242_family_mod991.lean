-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod991
-- name    : ErdosStraus242.family_mod991
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:24.842128+00:00
-- url     : https://prove2.me/theorems/980a671f-2bb8-480e-be8c-eb10f60c1360
-- title:
--   Seven Erdős–Straus congruence families modulo 991
-- statement:
--   For every integer $n>2$ with $n\bmod 991\in\{987, 983, 975, 959, 867, 743, 495\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=991$, where $\alpha=248$ and $g$ runs over the divisors $\{1, 2, 4, 8, 31, 62, 124\}$ of $248$; a class is $n\equiv -4g\pmod{991}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $991=4\cdot248-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid248$, $g<248$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod991 (n : ℕ) (hn : 2 < n)
    (hmod : n % 991 ∈ ({987, 983, 975, 959, 867, 743, 495} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
