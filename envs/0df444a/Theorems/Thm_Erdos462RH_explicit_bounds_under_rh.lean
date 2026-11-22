-- Prove2me | Theorems.Thm_Erdos462RH_explicit_bounds_under_rh
-- name    : Erdos462RH.explicit_bounds_under_rh
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:08:14.891914+00:00
-- url     : https://prove2.me/theorems/5bb3db14-c2d5-4705-922c-ae3e46dfc19c
-- title:
--   Balanced semiprimes in every sufficiently large window under RH
-- statement:
--   Assume classical RH. For each real $x\ge9.6\cdot10^{37}$ there are at least $(14/3)\sqrt{x}$ distinct integers $pq$ strictly between $x$ and $x+384\sqrt{x}(\log x)^2$, with $p,q$ prime and $\sqrt{x}/2<q<\sqrt{x}<p<3\sqrt{x}$. Their total least-prime-factor weight is at least $14/9$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Theorem 1.1; P. Erdős and R. L. Graham, Old and New Problems and Results in Combinatorial Number Theory, p. 92.

import Definitions.Def_Erdos462Balanced

namespace Erdos462RH
theorem explicit_bounds_under_rh (h : RiemannHypothesis) : ExplicitBounds := by sorry
end Erdos462RH
