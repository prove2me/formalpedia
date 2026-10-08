-- Prove2me | Theorems.Thm_DiffVI_Exist_lemma_6_1
-- name    : DiffVI.Exist.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:16.277085+00:00
-- url     : https://prove2.me/theorems/2d712d5f-507c-434c-a30c-bef38b781883
-- title:
--   Lemma 6.1 [Deimling], pp. 28–29 — a usc DI with nonempty closed convex values and linear growth has a weak solution on [0, T]
-- statement:
--   Let $T>0$, $\Omega=[0,T]\times\mathbb R^n$, and let $\mathbf F:\Omega\rightrightarrows\mathbb R^n$ be an upper semicontinuous set-valued map whose values $\mathbf F(t,x)$ are nonempty, closed and convex for every $(t,x)\in\Omega$. Suppose there is $\rho_{\mathbf F}>0$ with
--   $$\sup\{\|y\|: y\in\mathbf F(t,x)\}\le\rho_{\mathbf F}(1+\|x\|)\qquad\forall (t,x)\in\Omega.\qquad(6.1)$$
--   Then for every $x^0\in\mathbb R^n$ the differential inclusion $\dot x\in\mathbf F(t,x)$, $x(0)=x^0$, has a weak solution in the sense of Carathéodory on the whole interval $[0,T]$: an $x$ with $x(t)=x^0+\int_0^t v(s)\,ds$ for an integrable $v$ satisfying $v(t)\in\mathbf F(t,x(t))$ for almost every $t\in[0,T]$.
--
--   This is the existence theorem for convex-valued differential inclusions (Deimling, *Multivalued Differential Equations*, Theorem 5.1) on which the paper's existence theory for DVIs rests.
--
--   **Formalization Note** Upper semicontinuity is the open-neighbourhood form relative to $\Omega$. The paper cites this result without proof.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 28–29, Lemma 6.1 ([32, Theorem 5.1]), (6.1)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Lemma 6.1 ([32, Theorem 5.1], Deimling), pp. 28–29: an upper semicontinuous set-valued map on
`Ω = [0, T] × ℝⁿ` with nonempty closed convex values and the linear growth (6.1) admits, for every
`x⁰`, a weak (Carathéodory) solution of `ẋ ∈ 𝐅(t, x)`, `x(0) = x⁰` on all of `[0, T]`. -/
theorem lemma_6_1 {n : ℕ} (T : ℝ) (hT : 0 < T)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (husc : IsUSCOnΩ T Φ)
    (hne : ∀ t ∈ Set.Icc 0 T, ∀ x, (Φ t x).Nonempty)
    (hcl : ∀ t ∈ Set.Icc 0 T, ∀ x, IsClosed (Φ t x))
    (hcv : ∀ t ∈ Set.Icc 0 T, ∀ x, Convex ℝ (Φ t x))
    (hgrowth : ∃ ρF : ℝ, 0 < ρF ∧
      ∀ t ∈ Set.Icc 0 T, ∀ x, ∀ y ∈ Φ t x, ‖y‖ ≤ ρF * (1 + ‖x‖)) :
    ∀ x0 : EuclideanSpace ℝ (Fin n), ∃ x : ℝ → EuclideanSpace ℝ (Fin n),
      IsDIWeakSolution T Φ x0 x := by sorry

end DiffVI.Exist
