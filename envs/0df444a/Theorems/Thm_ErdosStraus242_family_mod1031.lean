-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1031
-- name    : ErdosStraus242.family_mod1031
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:44.492133+00:00
-- url     : https://prove2.me/theorems/92b1391e-d761-4983-8438-74bff3b8e10b
-- title:
--   Seven Erdős–Straus congruence families modulo 1031
-- statement:
--   For every integer $n>2$ with $n\bmod 1031\in\{1027, 1023, 1019, 1007, 859, 687, 515\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1031$, where $\alpha=258$ and $g$ runs over the divisors $\{1, 2, 3, 6, 43, 86, 129\}$ of $258$; a class is $n\equiv -4g\pmod{1031}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1031=4\cdot258-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid258$, $g<258$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1031 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1031 ∈ ({1027, 1023, 1019, 1007, 859, 687, 515} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
