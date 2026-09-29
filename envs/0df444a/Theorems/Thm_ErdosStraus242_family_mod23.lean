-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod23
-- name    : ErdosStraus242.family_mod23
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T20:47:43.789516+00:00
-- url     : https://prove2.me/theorems/98ac4561-c277-44b1-866d-c3930c24e33c
-- title:
--   Erdős–Straus congruence family modulo 23
-- statement:
--   For every natural number $n>2$ with $n \bmod 23 \in \{7,10,11,15,17,19,20,21,22\}$ there exist natural numbers $1\le x<y<z$ with
--   $$\frac4n=\frac1x+\frac1y+\frac1z .$$
--
--   The nine classes come from the Bloom–Elsholtz parametrization: whenever positive integers $a,b,c,d$ satisfy $cn+a=(4acd-1)b$, one has
--   $$\frac4n=\frac1{abd}+\frac1{acdn}+\frac1{bcdn}.$$
--   Taking $4acd-1=23$, i.e. $acd=6$, each factorization $(a,c,d)$ of $6$ solves $cn+a\equiv0\pmod{23}$ on one residue class, namely $n\equiv-ac^{-1}\pmod{23}$. The nine triples
--   $$(2,3,1),(3,2,1),(1,2,3),(1,3,2),(6,1,1),(1,6,1),(3,1,2),(2,1,3),(1,1,6)$$
--   give the classes $7,10,11,15,17,19,20,21,22$ in this order.
--
--   For $n=23k+r$ the resulting denominators are polynomials in $k$; strict increase fails only for the finitely many inputs $n\in\{7,10,11,17,20,21,22,33,40,43,44,63,66,86,109,132\}$, each of which has an explicit distinct witness.
--
--   The statement carries no primality assumption; the hypothesis $n>2$ is stated for uniformity with the other congruence families of this mission.
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242. The congruence family is the specialization of the Bloom–Elsholtz parametrization $cn+a=(4acd-1)b$, p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. The choice of the parameters and the treatment of the finitely many exceptional inputs are made here.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod23 (n : ℕ) (hn : 2 < n)
    (hmod : n % 23 ∈ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ)) : IsErdosStraus n := by sorry
end ErdosStraus242
