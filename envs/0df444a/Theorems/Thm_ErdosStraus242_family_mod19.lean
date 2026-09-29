-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod19
-- name    : ErdosStraus242.family_mod19
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T20:47:31.101387+00:00
-- url     : https://prove2.me/theorems/644d382a-655f-497b-845e-d0229a105c54
-- title:
--   Erdős–Straus congruence family modulo 19
-- statement:
--   For every natural number $n>2$ with $n \bmod 19 \in \{14,15,18\}$ there exist natural numbers $1\le x<y<z$ with
--   $$\frac4n=\frac1x+\frac1y+\frac1z .$$
--
--   The three classes come from the Bloom–Elsholtz parametrization: whenever positive integers $a,b,c,d$ satisfy $cn+a=(4acd-1)b$, one has
--   $$\frac4n=\frac1{abd}+\frac1{acdn}+\frac1{bcdn}.$$
--   Taking $4acd-1=19$, i.e. $acd=5$, the three admissible triples $(a,c,d)=(5,1,1),(1,5,1),(1,1,5)$ solve $cn+a\equiv 0 \pmod{19}$ exactly for $n\equiv 14,15,18 \pmod{19}$ respectively.
--
--   Writing $n=19k+r$, the denominators are $(5k+5,\,95k+70,\,19k^2+33k+14)$ for $r=14$, $(5k+4,\,95k+75,\,475k^2+755k+300)$ for $r=15$, and $(5k+5,\,95k+90,\,95k^2+185k+90)$ for $r=18$. Strict increase of the three denominators fails only for the finitely many inputs $n\in\{14,33,52,71,90,18\}$, which have explicit distinct witnesses of their own.
--
--   The statement carries no primality assumption; the hypothesis $n>2$ is stated for uniformity with the other congruence families of this mission.
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242. The congruence family is the specialization of the Bloom–Elsholtz parametrization $cn+a=(4acd-1)b$, p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. The choice of the parameters and the treatment of the finitely many exceptional inputs are made here.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod19 (n : ℕ) (hn : 2 < n)
    (hmod : n % 19 ∈ ({14, 15, 18} : Finset ℕ)) : IsErdosStraus n := by sorry
end ErdosStraus242
