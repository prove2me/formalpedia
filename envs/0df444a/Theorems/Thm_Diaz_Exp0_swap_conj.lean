-- Prove2me | Theorems.Thm_Diaz_Exp0_swap_conj
-- name    : Diaz.Exp0_swap_conj
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:05.745718+00:00
-- url     : https://prove2.me/theorems/4c648629-b631-40fe-9d1f-923790ea7e4c
-- title:
--   The formal exponential commutes with the involution: $\mathrm{Exp}_0 \circ \sigma = \overline{\phantom{x}} \circ \mathrm{Exp}_0$
-- statement:
--   For every pair of rationals $x = (a,b)$, regarding the values of $\mathrm{Exp}_0$ as complex numbers,
--
--   $$\mathrm{Exp}_0(b, a)  =  \overline{\mathrm{Exp}_0(a,b)} .$$
--
--   **Why.** Two ingredients. First $\mathrm{Exp}_0(b,a) = 2^{\,b+a} = 2^{\,a+b} = \mathrm{Exp}_0(a,b)$, the exponent being symmetric. Second, the value is a *real* number, so complex conjugation fixes it.
--
--   **Role.** In the coordinates $(a,b) \mapsto a t + b \bar t$ the involution of the model acts by swapping $a$ and $b$ (`Diaz.conj_coords`). The model asks for a formal exponential that commutes with the involution; this is that requirement, stated with complex conjugation on the right rather than merely with the coordinate swap, so that it is directly about the arithmetic situation rather than about a bookkeeping symmetry. Together with additivity and algebraicity of values, it completes the list of constraints the model imposes — and the point of the accompanying note is that those constraints do not force the kernel and torsion behaviour a proof of Diaz's conjecture would need.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L92-L97

import Mathlib
import Definitions.Def_Diaz_Exponential

open ComplexConjugate
open Diaz

theorem Diaz.Exp0_swap_conj (x : ℚ × ℚ) :
    ((Exp0 (x.2, x.1) : ℂ)) = (starRingEnd ℂ) ((Exp0 x : ℂ)) := by sorry
