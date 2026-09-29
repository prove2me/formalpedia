-- Prove2me | Theorems.Thm_Diaz_Exp0_pow_eq_one_iff
-- name    : Diaz.Exp0_pow_eq_one_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:07.026724+00:00
-- url     : https://prove2.me/theorems/0a75b7e1-52b6-4741-8a4c-2eece324b03f
-- title:
--   The image of the formal exponential is torsion-free
-- statement:
--   For every pair of rationals $x$ and every integer $n \geq 1$,
--
--   $$\mathrm{Exp}_0(x)^{\,n} = 1 \qquad\Longleftrightarrow\qquad \mathrm{Exp}_0(x) = 1 .$$
--
--   **Why.** With $x = (a,b)$ and $s = a+b$, $\mathrm{Exp}_0(x)^{n} = 2^{\,sn}$, and $2^{r} = 1$ holds for a real $r$ only at $r = 0$. So $sn = 0$, and $n \neq 0$ forces $s = 0$, which is exactly $\mathrm{Exp}_0(x) = 1$. The converse is trivial.
--
--   **Role.** This is the second of the two defects that §4 of the accompanying note turns on. In the intended shape of a proof of Diaz's conjecture, the kernel of the true exponential is the lattice $2\pi i\,\mathbb{Z}$, and a standard kernel $\mathbb{Z}\omega$ makes $\mathrm{Exp}(p\omega/m)$ a primitive $m$-th root of unity — so the image would contain every root of unity. The image $2^{\mathbb{Q}}$ of this $\mathrm{Exp}_0$ contains no root of unity except $1$.
--
--   **A caveat that matters, and that the source is careful about.** This is a fact about *this* $\mathrm{Exp}_0$, not about the model. The model's only constraints are that the formal exponential be a homomorphism into the algebraic numbers commuting with the involution, and those are also met by $\mathrm{Exp}'(a,b) = e^{2\pi i (a-b)}\,2^{\,a+b}$, whose kernel *is* a rank-one lattice and whose image *does* have torsion. What escapes the model is therefore not discreteness as such but the archimedean size of $2\pi i$.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L116-L138

import Mathlib
import Definitions.Def_Diaz_Exponential

open ComplexConjugate
open Diaz

theorem Diaz.Exp0_pow_eq_one_iff (x : ℚ × ℚ) {n : ℕ} (hn : n ≠ 0) :
    Exp0 x ^ n = 1 ↔ Exp0 x = 1 := by sorry
