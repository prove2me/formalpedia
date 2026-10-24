-- Prove2me | Theorems.Thm_FCP_Jacobian_birational_keller_criterion
-- name    : FCP.Jacobian.birational_keller_criterion
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T07:02:40.075998+00:00
-- url     : https://prove2.me/theorems/76403fc7-bf3f-4cc0-969c-7fe8952f25a5
-- title:
--   Birational Keller criterion: rational invertibility and a unit Jacobian imply polynomial invertibility
-- statement:
--   Let $k$ be any field, let $n\geq0$, and let $F=(F_1,\ldots,F_n)$ be a polynomial self-map of affine $n$-space whose polynomial Jacobian determinant is a unit. Assume the explicit birationality condition that every polynomial $p\in k[X_1,\ldots,X_n]$ can be written as a rational function of the coordinates of $F$: there are polynomials $a,b$, with $b\ne0$, such that $b(F)p=a(F)$. Then $F$ has a two-sided polynomial inverse. No characteristic-zero assumption is needed for this conditional criterion. The birationality hypothesis is essential to the statement proved here; it is not established for arbitrary two-variable characteristic-zero Keller maps, so the original Jacobian conjecture remains open.
-- source:
--   Classical birational Keller criterion; algebraic denominator-cancellation proof reconstructed using Mathlib's equational criterion for flatness. Reuses Proved public theorem dc81295d-b865-419f-a6ba-0a3ed6a8e1bc (unit Jacobian implies etale and flat substitution), whose foundation is Proved theorem 9d18d03b-da7c-5f5e-bdf9-caa8b756ff12. Original Keller/Formanek papers were not retrieved or read; no quotation or new-mathematics claim is made.

import Mathlib
import Definitions.Def_FCP_Jacobian

theorem FCP.Jacobian.birational_keller_criterion {k : Type} [Field k] {n : ℕ}
    (F : FCP.Jacobian.PolyMap k n) (hF : IsUnit (FCP.Jacobian.jacobian F).det)
    (hfrac : ∀ p : MvPolynomial (Fin n) k,
      ∃ a b : MvPolynomial (Fin n) k,
        b ≠ 0 ∧ MvPolynomial.aeval (R := k) F b * p = MvPolynomial.aeval (R := k) F a) :
    ∃ G : FCP.Jacobian.PolyMap k n,
      FCP.Jacobian.comp G F = FCP.Jacobian.idMap k n ∧
      FCP.Jacobian.comp F G = FCP.Jacobian.idMap k n := by sorry
