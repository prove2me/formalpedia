-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_aon_reduction
-- name    : AgriChain.LandAlloc.aon_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:07.254218+00:00
-- url     : https://prove2.me/theorems/f8dfd783-2bba-4599-ad53-3747007be3a2
-- title:
--   §3, p. 18 — under all-or-nothing yields F_i reduces to the two outcomes in which farmer i harvests
-- statement:
--   In the two-region agri-chain under its standing assumptions, let the EXP-crop yields be all-or-nothing, $Y^e_i\in\{H,0\}$, with arbitrary joint probabilities $h_{aa},h_{an},h_{na},h_{nn}$. For all land allocations $x_1,x_2\ge0$, the expected profits (13)–(14) reduce to
--   $$F_1(x_1,x_2)=h_{an}f_1(x_1H,0)+h_{aa}f_1(x_1H,x_2H)-x_1U_1+A_1,$$
--   $$F_2(x_1,x_2)=h_{na}f_2(0,x_2H)+h_{aa}f_2(x_1H,x_2H)-x_2U_2+A_2 .$$
--   A farmer with no harvest earns nothing from the EXP-crop, so only the outcomes in which her own yield is $H$ contribute.
--
--   This two-term form is the starting point of the equilibrium analysis of §3.
--
--   **Formalization Note.** The second display is printed as "$h_{na}f_2(0,x_2H,)$"; the stray comma is a typo. No hypothesis on the probabilities is needed.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 18, §3

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem aon_reduction (C : Chain) (hC : C.Standing) (Y : AON) (U1 U2 A1 A2 x1 x2 : ℝ)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) :
    F1 C Y U1 A1 x1 x2 =
        Y.han * f1 C (x1 * Y.H) 0 + Y.haa * f1 C (x1 * Y.H) (x2 * Y.H) - x1 * U1 + A1 ∧
      F2 C Y U2 A2 x1 x2 =
        Y.hna * f2 C 0 (x2 * Y.H) + Y.haa * f2 C (x1 * Y.H) (x2 * Y.H) - x2 * U2 + A2 := by sorry

end AgriChain.LandAlloc
