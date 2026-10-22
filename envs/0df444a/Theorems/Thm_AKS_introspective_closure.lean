-- Prove2me | Theorems.Thm_AKS_introspective_closure
-- name    : AKS.introspective_closure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:52:22.695854+00:00
-- url     : https://prove2.me/theorems/c64cd94f-07e1-4938-82e6-baa3f1ae6e85
-- title:
--   Introspective numbers and polynomials are closed under multiplication (Lemmas 4.5 and 4.6)
-- statement:
--   Lemmas 4.5 and 4.6 of the paper. Introspection, the relation of Definition 4.4 - m is introspective for f when f^m = f(X^m) modulo X^r - 1 over F_p - is closed under the two multiplications that matter for the correctness proof. Lemma 4.5: if m and m' are introspective for f, then so is m m', because f^(m m') = f(X^m)^(m') = f(X^(m m')) modulo X^r - 1, using that X^r - 1 divides X^(m r) - 1. Lemma 4.6: if m is introspective for f and for g, then it is introspective for f g, because (f g)^m = f^m g^m = f(X^m) g(X^m) modulo X^r - 1. Together they imply that every number of the set I = {(n/p)^i p^j} is introspective for every polynomial of the set P of products of X, X+1, ..., X+ell.
--
--   **Formalization Note** The two closures are stated as one conjunction over the definition introspective p r f m; the paper's consequence - I is introspective for P - is the goal's work, via the congruences (3), (4), and (5).
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 4 (Lemmas 4.5-4.6).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Lemmas 4.5 and 4.6 of the paper: introspection is closed under
multiplication of numbers and of polynomials.  -/
theorem introspective_closure (p r : ℕ)
    (f g : Polynomial (ZMod p)) (m m' : ℕ)
    (hm : introspective p r f m) (hm' : introspective p r f m')
    (hgm : introspective p r g m) :
    introspective p r f (m * m') ∧ introspective p r (f * g) m := by sorry

end AKS
