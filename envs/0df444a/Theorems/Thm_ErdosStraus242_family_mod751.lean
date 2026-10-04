-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod751
-- name    : ErdosStraus242.family_mod751
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:27.43124+00:00
-- url     : https://prove2.me/theorems/bb208858-3ba2-4507-a1e0-59bd201154f9
-- title:
--   Five Erdős–Straus congruence families modulo 751
-- statement:
--   For every integer $n>2$ with $n\bmod 751\in\{747, 743, 735, 563, 375\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=751$, where $\alpha=188$ and $g$ runs over the divisors $\{1, 2, 4, 47, 94\}$ of $188$; a class is $n\equiv -4g\pmod{751}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $751=4\cdot188-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid188$, $g<188$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod751 (n : ℕ) (hn : 2 < n)
    (hmod : n % 751 ∈ ({747, 743, 735, 563, 375} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
