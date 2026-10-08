-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod943
-- name    : ErdosStraus242.family_mod943
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:10.685814+00:00
-- url     : https://prove2.me/theorems/8a01b6a7-618b-44b1-8000-21500601bef8
-- title:
--   Five Erdős–Straus congruence families modulo 943
-- statement:
--   For every integer $n>2$ with $n\bmod 943\in\{939, 935, 927, 707, 471\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=943$, where $\alpha=236$ and $g$ runs over the divisors $\{1, 2, 4, 59, 118\}$ of $236$; a class is $n\equiv -4g\pmod{943}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $943=4\cdot236-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid236$, $g<236$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod943 (n : ℕ) (hn : 2 < n)
    (hmod : n % 943 ∈ ({939, 935, 927, 707, 471} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
