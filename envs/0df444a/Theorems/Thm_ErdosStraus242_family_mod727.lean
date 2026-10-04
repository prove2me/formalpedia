-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod727
-- name    : ErdosStraus242.family_mod727
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:21.530326+00:00
-- url     : https://prove2.me/theorems/1922c262-cf18-498e-93d8-dc051c3f1da5
-- title:
--   Seven Erdős–Straus congruence families modulo 727
-- statement:
--   For every integer $n>2$ with $n\bmod 727\in\{723, 719, 699, 675, 671, 623, 363\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=727$, where $\alpha=182$ and $g$ runs over the divisors $\{1, 2, 7, 13, 14, 26, 91\}$ of $182$; a class is $n\equiv -4g\pmod{727}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $727=4\cdot182-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid182$, $g<182$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod727 (n : ℕ) (hn : 2 < n)
    (hmod : n % 727 ∈ ({723, 719, 699, 675, 671, 623, 363} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
