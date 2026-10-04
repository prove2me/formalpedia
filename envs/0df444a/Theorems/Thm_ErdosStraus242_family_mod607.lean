-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod607
-- name    : ErdosStraus242.family_mod607
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:31:52.728703+00:00
-- url     : https://prove2.me/theorems/95edac03-cc88-4428-8a5c-1bec89d761a0
-- title:
--   Seven Erdős–Straus congruence families modulo 607
-- statement:
--   For every integer $n>2$ with $n\bmod 607\in\{603, 599, 591, 575, 531, 455, 303\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=607$, where $\alpha=152$ and $g$ runs over the divisors $\{1, 2, 4, 8, 19, 38, 76\}$ of $152$; a class is $n\equiv -4g\pmod{607}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $607=4\cdot152-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid152$, $g<152$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod607 (n : ℕ) (hn : 2 < n)
    (hmod : n % 607 ∈ ({603, 599, 591, 575, 531, 455, 303} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
