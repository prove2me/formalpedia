-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift
-- name    : AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/754466b7-b9f5-54ca-b924-aff8700a78e5
-- title:
--   Integrability of the real-place intertwining atom and its Möbius shift
-- statement:
--   Fix real numbers $a,b,c,d$ with $ad-bc \neq 0$, an integer $k$, and a real $\sigma > 0$. Introduce the $\mathbb{C}$-valued function of two real variables
--   $$\mathrm{atom}(\sigma, x) = \left(\frac{x - i}{\sqrt{1+x^{2}}}\right)^{k} \cdot (1+x^{2})^{-(\sigma + 1/2)},$$
--   where the integer power is the complex zpow of the quotient of the coercions of $x$ and $\sqrt{1+x^{2}}$, and the second factor is the complex power of the (positive real, coerced) base $1+x^{2}$ with complex exponent $-(\sigma + 1/2)$. The assertion is a conjunction of two statements about Lebesgue integrability of $\mathbb{C}$-valued functions on $\mathbb{R}$: first, that $x \mapsto \mathrm{atom}(\sigma, x)$ is integrable; and second, that the function
--   $$x \mapsto |ad-bc|^{\sigma + 1/2} \, |a + xc|^{-(2\sigma + 1)} \, \mathrm{atom}\!\left(\sigma, \frac{b + xd}{a + xc}\right)$$
--   is integrable, the two modulus factors again being complex powers of coerced nonnegative reals with complex exponents (so the middle factor is $0$ at the single point where $a + xc = 0$, by the Mathlib convention for `cpow` at base $0$).
--
--   The function $\mathrm{atom}(\sigma,\cdot)$ is the restriction to the big Bruhat cell of the weight-$k$ vector in a principal series of $\mathrm{GL}_2(\mathbb{R})$, and the second integrand is its translate by $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ together with the automorphy factor produced by the Bruhat decomposition; both integrands have absolute value comparable to $(1+x^{2})^{-(\sigma+1/2)}$. The result supplies the integrability needed to manipulate the archimedean Weyl intertwining integral, and is used in the analysis of its behaviour as $\sigma \to 1/2$ for flat families supported at the real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    Integrable (atom σ) ∧
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + x * d) / (a + x * c))) := by sorry
