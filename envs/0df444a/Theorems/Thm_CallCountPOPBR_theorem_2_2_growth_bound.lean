-- Prove2me | Theorems.Thm_CallCountPOPBR_theorem_2_2_growth_bound
-- name    : CallCountPOPBR.theorem_2_2_growth_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:51.729829+00:00
-- url     : https://prove2.me/theorems/8894cde1-6f3e-4ce1-aef0-6d273ab80210
-- title:
--   Growth bound $C_n\le 2^{n+1}-1$ (proof of Theorem 2.2)
-- statement:
--   Let $(N,d,p,\mathrm{Obs})$ be a well-formed POPBR instance, $(a_r,b_r)_{r<p}$ an admissible rule, and $C$ a completion of the instance under that rule. Then
--   $$
--   C_n\le 2^{n+1}-1\qquad(0\le n\le N).
--   $$
--
--   This bound shows that every generated value has $O(N)$ bits; it is what makes the verifier of Theorem 2.4 polynomial.
--
--   Differences from the source: none.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.2, p.4

import Definitions.Def_CallCountPOPBR_Instance_IsValid
import Definitions.Def_CallCountPOPBR_IsAdmissibleRule
import Definitions.Def_CallCountPOPBR_IsCompletion

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Growth bound `C_n ≤ 2^{n+1} − 1`** (proof of Theorem 2.2, cited by Theorem 2.4). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…),
proof of Theorem 2.2, p.4: "The numbers generated have polynomial bit length: inductively,
C_n ≤ 2^{n+1} − 1, because every child index is smaller than n."

For a well-formed instance, an admissible rule and a completion `C`, every `C_n` with `n ≤ N`
is at most `2^{n+1} − 1`. -/
theorem theorem_2_2_growth_bound (I : Instance) (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ)
    (hI : I.IsValid) (hrule : IsAdmissibleRule I.d I.p rule) (hC : IsCompletion I rule C) :
    ∀ n, n ≤ I.N → C n ≤ 2 ^ (n + 1) - 1 := by sorry

end CallCountPOPBR
