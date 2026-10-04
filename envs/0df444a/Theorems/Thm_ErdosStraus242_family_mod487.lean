-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod487
-- name    : ErdosStraus242.family_mod487
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:56:31.262348+00:00
-- url     : https://prove2.me/theorems/1d0080fb-eab9-4a6c-b0f8-46d4fe546641
-- title:
--   Three Erdős–Straus congruence families modulo 487
-- statement:
--   For every integer $n>2$ with $n\bmod 487\in\{483, 479, 243\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=487$, where $\alpha=122$ and $g$ runs over the divisors $\{1, 2, 61\}$ of $122$; a class is $n\equiv -4g\pmod{487}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $487=4\cdot122-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid122$, $g<122$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod487 (n : ℕ) (hn : 2 < n)
    (hmod : n % 487 ∈ ({483, 479, 243} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
