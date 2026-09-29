-- Prove2me | Theorems.Thm_FamousTheorems_lucas_lehmer_sufficiency
-- name    : FamousTheorems.lucas_lehmer_sufficiency
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:29.199412+00:00
-- url     : https://prove2.me/theorems/a2720453-80cf-4441-b070-6dce7260b2d4
-- title:
--   The Lucas–Lehmer primality test
-- statement:
--   **The Lucas\u2013Lehmer test.** For $p > 2$, the Mersenne number $M_p = 2^p - 1$ is prime if the Lucas\u2013Lehmer sequence $s_0 = 4$, $s_{k+1} = s_k^2 - 2$ satisfies $s_{p-2} \equiv 0 \pmod{M_p}$. The test decides primality of $M_p$ in $O(p)$ modular squarings, with no trial division and no randomness — astonishingly cheap for numbers of this size. That efficiency is why every record-holding largest known prime for decades has been a Mersenne prime, and it is the computational core of the GIMPS distributed search. The underlying reason is that the recurrence tracks powers of $2 + \sqrt3$ in a quadratic extension, and the congruence detects that this element has the order forced by $M_p$ being prime. Lucas devised the method in 1878 and Lehmer simplified it in 1930. **Formalization note.** This is the sufficiency direction: the congruence implies primality. The result is Mathlib's `lucas_lehmer_sufficiency`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem lucas_lehmer_sufficiency :
    ∀ (p : ℕ), 1 < p → LucasLehmerTest p → Nat.Prime (mersenne p) := by sorry

end FamousTheorems
