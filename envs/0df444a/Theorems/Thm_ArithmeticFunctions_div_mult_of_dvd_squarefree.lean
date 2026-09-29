-- Prove2me | Theorems.Thm_ArithmeticFunctions_div_mult_of_dvd_squarefree
-- name    : ArithmeticFunctions.div_mult_of_dvd_squarefree
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:29.330724+00:00
-- url     : https://prove2.me/theorems/5c453d5c-37c4-4698-add0-77a1f424a29d
-- title:
--   Multiplicative functions divide along divisors of a squarefree number
-- statement:
--   **For a multiplicative $f$ and squarefree $l$, the quotient $f(l)/f(d)$ is $f(l/d)$.**
--
--   Let $f$ be a multiplicative arithmetic function, $l$ squarefree and $d \mid l$ with
--   $f(d) \ne 0$. Then
--
--   $$\frac{f(l)}{f(d)} \;=\; f\!\left(\frac{l}{d}\right).$$
--
--   Squarefreeness is exactly what makes this work: it forces $d$ and $l/d$ to be **coprime**,
--   since any common prime would divide $l$ twice. Multiplicativity then gives
--   $f(l) = f(d)\,f(l/d)$, and dividing by the non-zero $f(d)$ yields the claim. Without
--   squarefreeness the conclusion fails — for instance with $f = \mathrm{id}^{0}$ variants or any
--   $f$ that is multiplicative but not completely multiplicative, $f(p^2) \ne f(p)f(p)$ in general.
--
--   This small identity is used constantly in sieve theory, where sums run over squarefree $l$
--   supported on the sifting primes and one repeatedly reindexes $l = d\cdot m$; Selberg's sieve in
--   particular manipulates $f(l)/f(d)$ throughout the optimisation of its quadratic form.
--
--   **Formalization note.** `ArithmeticFunction.IsMultiplicative` is multiplicativity on coprime
--   arguments together with $f(1) = 1$; the hypothesis $f(d) \ne 0$ makes the division meaningful.
-- source:
--   Standard in sieve theory; see Halberstam & Richert, *Sieve Methods*, and Friedlander & Iwaniec, *Opera de Cribro*. Lean proof extracted from `Salt/Brun/SelbergPort.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ArithmeticFunctions

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : f.IsMultiplicative)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) :
    f l / f d = f (l / d) := by sorry

end ArithmeticFunctions
