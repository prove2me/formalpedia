-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod559
-- name    : ErdosStraus242.family_mod559
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:57:12.251305+00:00
-- url     : https://prove2.me/theorems/0fa63a39-d9e7-4f70-9fae-54a3284f60cd
-- title:
--   Eleven Erdős–Straus congruence families modulo 559
-- statement:
--   For every integer $n>2$ with $n\bmod 559\in\{555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=559$, where $\alpha=140$ and $g$ runs over the divisors $\{1, 2, 4, 5, 7, 10, 14, 20, 28, 35, 70\}$ of $140$; a class is $n\equiv -4g\pmod{559}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $559=4\cdot140-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid140$, $g<140$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod559 (n : ℕ) (hn : 2 < n)
    (hmod : n % 559 ∈ ({555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
