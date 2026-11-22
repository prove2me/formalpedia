-- Prove2me | Theorems.Thm_Erdos462RH_explicit_bounds_of_selberg
-- name    : Erdos462RH.explicit_bounds_of_selberg
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:07:21.167574+00:00
-- url     : https://prove2.me/theorems/a2516822-0997-4f2f-a992-8312fa804c93
-- title:
--   The explicit semiprime bounds from the Selberg estimate
-- statement:
--   Assume the explicit theta Selberg estimate of Chirre and Hagen. For each real $x\ge9.6\cdot10^{37}$ there are at least $(14/3)\sqrt{x}$ distinct integers $pq$ strictly between $x$ and $x+384\sqrt{x}(\log x)^2$, with $p,q$ prime and $\sqrt{x}/2<q<\sqrt{x}<p<3\sqrt{x}$. Their total least-prime-factor weight is at least $14/9$. This is the implication proved by the accompanying Lean project.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Theorem 1.1, Section 2, formal verification; Erdos462RH.explicit_bounds_of_selberg.

import Definitions.Def_Erdos462Balanced
import Definitions.Def_Erdos462Selberg

namespace Erdos462RH
theorem explicit_bounds_of_selberg (h : SelbergBound) : ExplicitBounds := by sorry
end Erdos462RH
