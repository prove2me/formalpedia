-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_continuous_of_inW12
-- name    : AsymptoticOperator.exists_continuous_of_inW12
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:58:51.144994+00:00
-- url     : https://prove2.me/theorems/3aaff5e5-c575-4a94-a101-0b024b2d0c12
-- title:
--   Elements of $W^{1,2}(S^1,\mathbb{R}^{2n})$ have continuous representatives
-- statement:
--   Let $f\in L^2(S^1,\mathbb{R}^{2n})$, $S^1=\mathbb{R}/\mathbb{Z}$ with its Haar probability measure, and let $\hat f_k=\int_{S^1}e^{-2\pi i k t}f(t)\,dt\in\mathbb{C}^{2n}$ be its Fourier coefficients. If
--   $$\sum_{k\in\mathbb{Z}}(1+k^2)\,|\hat f_k|^2<\infty,$$
--   i.e. $f\in W^{1,2}(S^1,\mathbb{R}^{2n})$, then there is a continuous map $\varphi:S^1\to\mathbb{R}^{2n}$ with $f=\varphi$ almost everywhere.
--
--   This is the one-dimensional Sobolev embedding $W^{1,2}(S^1)\subset C^0(S^1)$ in the Fourier-coefficient description of $W^{1,2}$ used for asymptotic operators. It lets elements of the domain of $A_S=-J_0\partial_t-S$ be evaluated pointwise, for instance to compare kernel elements with solutions of the linear equation $\dot x=J_0Sx$.
--
--   **Formalization Note.** `L2 n` is `Lp (EuclideanSpace ℝ (Fin n ⊕ Fin n)) 2 haarAddCircle` on `UnitAddCircle`, and `InW12 f` is the summability over `ℤ` of `(1 + k²) * ∑ i, ‖coeff f k i‖²`, where `coeff f k` is `fourierCoeff` of the complexified representative (setting module). The conclusion is `∃ φ : C(UnitAddCircle, Vec n), ⇑f =ᵐ[haarAddCircle] ⇑φ`.
-- source:
--   Auxiliary statement for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 3, §3.4 p. 61 (kernel of the asymptotic operator)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

/-- Every element of `W^{1,2}(S¹, ℝ²ⁿ)` has a continuous representative: if `f ∈ L²` satisfies
`∑ₖ (1 + k²) |f̂ₖ|² < ∞`, then `f` agrees almost everywhere with a continuous loop. -/
theorem exists_continuous_of_inW12 {n : ℕ} (f : L2 n) (hf : InW12 f) :
    ∃ φ : C(UnitAddCircle, Vec n),
      (f : UnitAddCircle → Vec n) =ᵐ[AddCircle.haarAddCircle] (φ : UnitAddCircle → Vec n) := by
  sorry

end AsymptoticOperator
