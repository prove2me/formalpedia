-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod551
-- name    : ErdosStraus242.family_mod551
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:57:08.232824+00:00
-- url     : https://prove2.me/theorems/5a7b27f7-ee6d-4443-9e27-086fed007724
-- title:
--   Seven Erdős–Straus congruence families modulo 551
-- statement:
--   For every integer $n>2$ with $n\bmod 551\in\{547, 543, 539, 527, 459, 367, 275\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=551$, where $\alpha=138$ and $g$ runs over the divisors $\{1, 2, 3, 6, 23, 46, 69\}$ of $138$; a class is $n\equiv -4g\pmod{551}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $551=4\cdot138-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid138$, $g<138$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod551 (n : ℕ) (hn : 2 < n)
    (hmod : n % 551 ∈ ({547, 543, 539, 527, 459, 367, 275} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
