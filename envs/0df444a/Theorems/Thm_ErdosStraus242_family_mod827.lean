-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod827
-- name    : ErdosStraus242.family_mod827
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:36.599109+00:00
-- url     : https://prove2.me/theorems/c4cb600f-e25f-4b75-8e61-e8a412119081
-- title:
--   Five Erdős–Straus congruence families modulo 827
-- statement:
--   For every integer $n>2$ with $n\bmod 827\in\{823, 815, 791, 735, 551\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=827$, where $\alpha=207$ and $g$ runs over the divisors $\{1, 3, 9, 23, 69\}$ of $207$; a class is $n\equiv -4g\pmod{827}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $827=4\cdot207-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid207$, $g<207$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod827 (n : ℕ) (hn : 2 < n)
    (hmod : n % 827 ∈ ({823, 815, 791, 735, 551} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
