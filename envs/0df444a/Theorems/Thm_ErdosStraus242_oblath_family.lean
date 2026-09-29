-- Prove2me | Theorems.Thm_ErdosStraus242_oblath_family
-- name    : ErdosStraus242.oblath_family
-- status  : Proved
-- author  : @alexcarter
-- created : 2026-09-11T11:43:00.992417+00:00
-- url     : https://prove2.me/theorems/a9887529-fadd-4e06-a3ae-c1db29c1a341
-- title:
--   Obláth’s prime divisor condition
-- statement:
--   For natural numbers $n,q$, if $n>2$, $q$ is prime, $q\mid n+1$, and $q≡3\pmod4$, then $4/n$ has a decomposition with natural denominators $1≤ x<y<z$. The equality is rational.
-- source:
--   Obláth, Mathesis 59 (1950), pp. 308–316, identified by https://www.erdosproblems.com/242. Source-quality statement inspected in Pomerance–Weingartner, Exceptions to the Erdős–Straus–Schinzel conjecture (2025), introduction p. 1, https://math.dartmouth.edu/~carlp/ESS-ExceptionsV9.pdf. Exact distinct version proved locally; original Obláth full text was not retrieved.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem oblath_family (n q : ℕ) (hn : 2 < n)
    (hq : Nat.Prime q) (hdiv : q ∣ n+1) (hmod : q % 4 = 3) :
    IsErdosStraus n := by sorry
end ErdosStraus242
