-- Prove2me | Theorems.Thm_BNS2000_theorem_5_2
-- name    : BNS2000.theorem_5_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:09:11.594929+00:00
-- url     : https://prove2.me/theorems/87f0a9b2-d444-41e1-8b7e-63b50aab8479
-- title:
--   Inclusion Theorem — Embedding Bellantoni-Cook Safe Recursion into RA and RS (Theorem 5.2)
-- statement:
--   Theorem 5.2 (pp. 26-29): Every function `f(x⃗; y⃗)` in the Bellantoni-Cook algebra `BC` is represented by a closed `RA`-term (and `RS`-term) `t_f` of type `ι₁ → ⋯ → ι_m → ι₀ → ⋯ → ι₀ → ι₀` using higher-type safe recursion at type `ι₀ → ι₀`.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 5, Theorem 5.2, pp. 26-29.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 5.2** (Section 5, p. 27):
Every function `f(x⃗; y⃗)` in the Bellantoni–Cook safe recursion function algebra `B`
(`f : BCFunc m n`, which characterizes the polynomial-time computable functions) is
denoted by a closed `RA`-term `t_f` of type `!ι → ⋯ → !ι → ι → ⋯ → ι → ι`
(`RADenotesTwoSorted t_f (evalBC f)`). -/
theorem theorem_5_2
    {m n : Nat} (f : BCFunc m n) :
    ∃ t_f : Term, RADenotesTwoSorted t_f (evalBC f) := by
  sorry

end BNS2000
