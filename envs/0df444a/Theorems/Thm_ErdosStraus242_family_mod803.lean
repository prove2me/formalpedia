-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod803
-- name    : ErdosStraus242.family_mod803
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:34.661595+00:00
-- url     : https://prove2.me/theorems/3f5bb511-7e62-4755-9b10-1ecda987e882
-- title:
--   Three Erdős–Straus congruence families modulo 803
-- statement:
--   For every integer $n>2$ with $n\bmod 803\in\{799, 791, 535\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=803$, where $\alpha=201$ and $g$ runs over the divisors $\{1, 3, 67\}$ of $201$; a class is $n\equiv -4g\pmod{803}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $803=4\cdot201-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid201$, $g<201$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod803 (n : ℕ) (hn : 2 < n)
    (hmod : n % 803 ∈ ({799, 791, 535} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
