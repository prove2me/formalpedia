-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod743
-- name    : ErdosStraus242.family_mod743
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:25.977954+00:00
-- url     : https://prove2.me/theorems/71510524-1726-44dd-8a44-cdaeab9567ab
-- title:
--   Seven Erdős–Straus congruence families modulo 743
-- statement:
--   For every integer $n>2$ with $n\bmod 743\in\{739, 735, 731, 719, 619, 495, 371\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=743$, where $\alpha=186$ and $g$ runs over the divisors $\{1, 2, 3, 6, 31, 62, 93\}$ of $186$; a class is $n\equiv -4g\pmod{743}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $743=4\cdot186-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid186$, $g<186$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod743 (n : ℕ) (hn : 2 < n)
    (hmod : n % 743 ∈ ({739, 735, 731, 719, 619, 495, 371} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
