-- Prove2me | Theorems.Thm_APSCounting893_Main_scaled_odd_rational_bit_polynomial_time
-- name    : APSCounting893.Main.scaled_odd_rational_bit_polynomial_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T20:38:28.654195+00:00
-- url     : https://prove2.me/theorems/7eb9fd22-d1f5-45c8-a314-0d6d80204096
-- title:
--   Polynomial-time bit access to a scaled rational with odd denominator
-- statement:
--   There is one deterministic finite binary multitape Turing machine, with one polynomial clock, that receives nonnegative integers $a,p,H,q$ in binary and, whenever $p$ is odd, returns the requested bit
--   $$\operatorname{bit}_q\!\left(\left\lfloor\frac{a2^H}{p}\right\rfloor\right).$$
--   The running time is polynomial in the combined binary input length. The exponent $H$ and bit position $q$ need not be bounded by a polynomial in the numerical values of the other inputs.
--
--   This is a scaled form of the reciprocal-bit calculation in Chinese remainder conversion. It allows very long rational approximations to be accessed without constructing their expanded binary strings. The denominator $p=1$, the numerator zero, the exponent zero, and all bit positions are included.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, pp. 695–716, author manuscript p. 10, Lemma 4.2 and the Chinese remainder comparison argument of Lemma 4.3, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Scaled extension obtained by multiplying the reciprocal by the explicitly supplied integer a; used for the arithmetic-to-threshold step of Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf.

import Mathlib
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
set_option autoImplicit false

theorem APSCounting893.Main.scaled_odd_rational_bit_polynomial_time :
    ∃ f : ℕ × (ℕ × (ℕ × ℕ)) → Bool,
      Turing.MultiTapeTM.ComputableInPolyTime f
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
            (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat)))
        Turing.MultiTapeTM.encBool ∧
      ∀ a p H q : ℕ,Odd p → f (a,p,H,q)=(a*2^H/p).testBit q := by sorry
