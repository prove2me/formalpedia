-- Prove2me | Theorems.Thm_Diaz_conj_coords
-- name    : Diaz.conj_coords
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:26.78461+00:00
-- url     : https://prove2.me/theorems/a9deaa93-9cbb-4723-9410-d9fc8fe03ac4
-- title:
--   Complex conjugation acts on the rational plane by swapping coordinates
-- statement:
--   Let $t \in \mathbb{C}$ and let $a, b \in \mathbb{Q}$. Then
--
--   $$\overline{a\,t + b\,\bar t}  =  b\,t + a\,\bar t.$$
--
--   **Why.** Conjugation is a ring homomorphism fixing the rationals and is an involution, so it exchanges $t$ with $\bar t$ and leaves the coefficients alone.
--
--   **Role.** In the model the involution is complex conjugation, and this identity says that in the coordinates $(a,b) \mapsto a t + b\bar t$ it is simply the coordinate swap $(a,b) \mapsto (b,a)$. That is what licenses stating the involution — and the compatibility of the formal exponential $\mathrm{Exp}_0(a,b) = 2^{a+b}$ with it — purely in coordinates: $\mathrm{Exp}_0$ is symmetric in $a$ and $b$, so it commutes with $\sigma$ for free.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Model.lean#L144-L149

import Mathlib

open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem Diaz.conj_coords (t : ℂ) (a b : ℚ) :
    conj ((a : ℂ) * t + (b : ℂ) * conj t) = (b : ℂ) * t + (a : ℂ) * conj t := by sorry
