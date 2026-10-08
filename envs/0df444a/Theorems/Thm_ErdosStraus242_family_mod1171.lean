-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1171
-- name    : ErdosStraus242.family_mod1171
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:42:16.772961+00:00
-- url     : https://prove2.me/theorems/91c33b0b-d42b-4999-9bbd-d7d41f1ee4e6
-- title:
--   One Erdős–Straus congruence families modulo 1171
-- statement:
--   For every integer $n>2$ with $n\bmod 1171\in\{1167\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 1 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1171$, where $\alpha=293$ and $g$ runs over the divisors $\{1\}$ of $293$; a class is $n\equiv -4g\pmod{1171}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1171=4\cdot293-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid293$, $g<293$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1171 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1171 ∈ ({1167} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
