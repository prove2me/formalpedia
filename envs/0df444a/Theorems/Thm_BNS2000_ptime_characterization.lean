-- Prove2me | Theorems.Thm_BNS2000_ptime_characterization
-- name    : BNS2000.ptime_characterization
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:09:20.899147+00:00
-- url     : https://prove2.me/theorems/a39da23f-86c2-4263-9f64-dfc11038dbe0
-- title:
--   Characterization of the Polynomial-Time Functions by RA and RS
-- statement:
--   Main Result (Sections 4-5, pp. 21-29): The numerical functions definable by closed level-1 terms of `RA`, the numerical functions definable by closed level-1 terms of `RS`, and the polynomial-time computable functions (`BCFunc k 0`) coincide.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Sections 4-5, Theorems 5.1 and 5.2, pp. 21-29.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Characterization of Polynomial-Time Computability by Higher-Type Ramified Affinable Recursion**
(Sections 1 & 5, pp. 18, 26–27):
A numerical function `F : (Fin k → Nat) → Nat` is denoted by a closed `RA`-term `t` of type
`!ι → ⋯ → !ι → ι` if and only if `F` is computable in polynomial time (characterized via the
Bellantoni–Cook safe recursion function algebra `BCFunc k 0` together with a polynomial bound
`p_t` on the normalization complexity of `t (!n₁) ... (!nₖ)`). -/
theorem ptime_characterization
    (k : Nat) (F : (Fin k → Nat) → Nat) :
    (∃ t : Term, RADenotesTwoSorted (m := k) (n := 0) t (fun xs _ => F xs)) ↔
    (∃ f : BCFunc k 0, ∀ xs : Fin k → Nat, F xs = evalBC f xs Fin.elim0) := by
  sorry

end BNS2000
