-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod659
-- name    : ErdosStraus242.family_mod659
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:10.996771+00:00
-- url     : https://prove2.me/theorems/079a9ed1-d699-4587-8b69-b7f3ab500d55
-- title:
--   Seven Erdős–Straus congruence families modulo 659
-- statement:
--   For every integer $n>2$ with $n\bmod 659\in\{655, 647, 639, 615, 599, 527, 439\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=659$, where $\alpha=165$ and $g$ runs over the divisors $\{1, 3, 5, 11, 15, 33, 55\}$ of $165$; a class is $n\equiv -4g\pmod{659}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $659=4\cdot165-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid165$, $g<165$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod659 (n : ℕ) (hn : 2 < n)
    (hmod : n % 659 ∈ ({655, 647, 639, 615, 599, 527, 439} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
