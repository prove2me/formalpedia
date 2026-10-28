-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_eq_S5
-- name    : ClassicalShadow.Linear.eq_S5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:40.874049+00:00
-- url     : https://prove2.me/theorems/1284ba25-971c-45c0-a3e6-b42e2d07b662
-- title:
--   (S5), p. 11 — the single-shadow prediction is unbiased: E[tr(Oρ̂)] = tr(Oρ)
-- statement:
--   Let $\mathcal U$ be a finite, tomographically complete measurement primitive on $n$ qubits, $\rho$ a density operator and $O$ a Hermitian $2^n\times 2^n$ matrix. Let $\hat o = \operatorname{tr}(O\hat\rho)$ be the prediction obtained from one classical shadow $\hat\rho$ of $\rho$. Then
--   $$\mathbb E[\hat o] = \operatorname{tr}(O\rho),$$
--   the expectation being over the random unitary $U \sim \mathcal U$ and the Born-rule outcome $\hat b$.
--
--   A single classical shadow thus predicts any linear property correctly on average; Lemma 1 controls the fluctuations.
--
--   **Formalization Note.** Both sides are real parts of traces; for Hermitian $O$ and a state $\rho$ they are real.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 11, (S5)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem eq_S5 {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (ρ : Op n) (hρ : WildeQIT.IsDensityOperator ρ)
    (O : Op n) (hO : O.IsHermitian) :
    snapMean E ρ O = (O * ρ).trace.re := by sorry
end ClassicalShadow.Linear
