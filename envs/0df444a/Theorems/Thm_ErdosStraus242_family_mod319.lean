-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod319
-- name    : ErdosStraus242.family_mod319
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:38:03.940734+00:00
-- url     : https://prove2.me/theorems/e0e24d60-4484-49a7-9f1c-448d3c04d775
-- title:
--   Nine Erdős–Straus congruence families modulo 319
-- statement:
--   For every integer $n>2$ with $n\bmod 319\in\{315, 311, 303, 299, 287, 279, 255, 239, 159\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The nine classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=319$, where $\alpha=80$ and $g$ runs over the divisors \{1,2,4,5,8,10,16,20,40\} of $80$; a class is $n\equiv -4g\pmod{319}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $319=4\cdot80-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$ with $g\in\{1,2,4,5,8,10,16,20,40\}$ the divisors of $80$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod319 (n : ℕ) (hn : 2 < n)
    (hmod : n % 319 ∈ ({315, 311, 303, 299, 287, 279, 255, 239, 159} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
