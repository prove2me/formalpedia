-- Prove2me | Theorems.Thm_BNS2000_theorem_3_1
-- name    : BNS2000.theorem_3_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:08:11.209944+00:00
-- url     : https://prove2.me/theorems/af34efec-8aba-46ba-b515-02995cb6922d
-- title:
--   Polynomial-Time Normalization of First-Order Ramified Terms
-- statement:
--   Theorem 3.1 (p. 20): Every first-order ramified term can be normalized in time polynomial in the lengths of its free variables, and every ground-type term without free variables of higher type reduces to a unique normal form.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 3, Theorem 3.1, p. 20.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 3.1 (Closure under reduction)** (Section 3, p. 21):
Let `r` be an `RA`-term.
(1) If `r → r'`, then `r'` is an `RA`-term.
(2) If `x` is affinable in `r` (with `x` incomplete) and `nf_r` is the normal form `nf(r)`,
    then `x` is affinable in `nf(r)`. -/
theorem theorem_3_1 (r : Term) (hr : IsRATerm r) :
    (∀ r' : Term, Step r r' → IsRATerm r') ∧
    (∀ (x : Var) (nf_r : Term),
      x.ty.isIncomplete = true →
      IsAffinable x r →
      IsNormalFormOf r nf_r →
      IsAffinable x nf_r) := by
  sorry

end BNS2000
