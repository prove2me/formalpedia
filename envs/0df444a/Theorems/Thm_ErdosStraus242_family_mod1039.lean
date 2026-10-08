-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1039
-- name    : ErdosStraus242.family_mod1039
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:46.6906+00:00
-- url     : https://prove2.me/theorems/d340b77e-b877-4042-93b8-9b64e28731fd
-- title:
--   Eleven Erdős–Straus congruence families modulo 1039
-- statement:
--   For every integer $n>2$ with $n\bmod 1039\in\{1035, 1031, 1023, 1019, 999, 987, 959, 935, 831, 779, 519\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1039$, where $\alpha=260$ and $g$ runs over the divisors $\{1, 2, 4, 5, 10, 13, 20, 26, 52, 65, 130\}$ of $260$; a class is $n\equiv -4g\pmod{1039}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1039=4\cdot260-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid260$, $g<260$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1039 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1039 ∈ ({1035, 1031, 1023, 1019, 999, 987, 959, 935, 831, 779, 519} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
