-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1147
-- name    : ErdosStraus242.family_mod1147
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:42:07.343961+00:00
-- url     : https://prove2.me/theorems/a4326c33-46b7-4481-88db-8ca5406a7994
-- title:
--   Three Erdős–Straus congruence families modulo 1147
-- statement:
--   For every integer $n>2$ with $n\bmod 1147\in\{1143, 1119, 983\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1147$, where $\alpha=287$ and $g$ runs over the divisors $\{1, 7, 41\}$ of $287$; a class is $n\equiv -4g\pmod{1147}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1147=4\cdot287-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid287$, $g<287$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1147 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1147 ∈ ({1143, 1119, 983} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
