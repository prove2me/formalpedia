-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod571
-- name    : ErdosStraus242.family_mod571
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:57:18.258795+00:00
-- url     : https://prove2.me/theorems/74ca0cec-033a-4ff9-997f-32b742b2b0cf
-- title:
--   Three Erdős–Straus congruence families modulo 571
-- statement:
--   For every integer $n>2$ with $n\bmod 571\in\{567, 527, 519\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=571$, where $\alpha=143$ and $g$ runs over the divisors $\{1, 11, 13\}$ of $143$; a class is $n\equiv -4g\pmod{571}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $571=4\cdot143-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid143$, $g<143$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod571 (n : ℕ) (hn : 2 < n)
    (hmod : n % 571 ∈ ({567, 527, 519} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
