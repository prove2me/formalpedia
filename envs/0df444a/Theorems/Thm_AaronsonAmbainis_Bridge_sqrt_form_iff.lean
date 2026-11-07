-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sqrt_form_iff
-- name    : AaronsonAmbainis.Bridge.sqrt_form_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:12:13.421865+00:00
-- url     : https://prove2.me/theorems/d99e1ff8-0a20-4684-a8fa-4abd0a3b151e
-- title:
--   Bridge: sqrt form iff
-- statement:
--   A bound without square roots and its printed form: if `ε, I, c₁ ≥ 0`, `D, c₂, m > 0` and
--   `15 c₁² m = k c₂²`, then `I ≥ (c₁ √15 / (c₂ π^4)) ε^{5/2} / D^6` if and only if
--   `k ε^5 ≤ m π^8 D^12 I²`. The power `ε^{5/2}` is written `ε² √ε`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L224-L256
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L224-L256

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.sqrt_form_iff {c₁ c₂ k m ε D I : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (hm : 0 < m)
    (hkm : 15 * c₁ ^ 2 * m = k * c₂ ^ 2) (hε : 0 ≤ ε) (hD : 0 < D) (hI : 0 ≤ I) :
    c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6 ≤ I
      ↔ k * ε ^ 5 ≤ m * Real.pi ^ 8 * D ^ 12 * I ^ 2 := by sorry
