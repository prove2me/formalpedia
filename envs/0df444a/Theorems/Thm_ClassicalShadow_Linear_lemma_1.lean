-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_lemma_1
-- name    : ClassicalShadow.Linear.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:50.416419+00:00
-- url     : https://prove2.me/theorems/84ce918b-2ebe-4f40-8563-f18378e6819b
-- title:
--   Lemma 1, p. 11, (S6) — Var[tr(Oρ̂)] ≤ ‖O − tr(O)/2ⁿ 𝕀‖²_shadow
-- statement:
--   Let $\mathcal U$ be a finite, tomographically complete measurement primitive on $n$ qubits, $\rho$ a density operator and $O$ a Hermitian $2^n\times 2^n$ matrix. Let $\hat o = \operatorname{tr}(O\hat\rho)$, where $\hat\rho$ is a classical shadow of $\rho$. Then
--   $$\operatorname{Var}[\hat o] = \mathbb E\big[(\hat o - \mathbb E[\hat o])^2\big] \le \Big\| O - \frac{\operatorname{tr}(O)}{2^n}\mathbb I \Big\|_{\mathrm{shadow}}^2 ,$$
--   where $\|\cdot\|_{\mathrm{shadow}}$ is the shadow norm (S7), a maximum over all states, which depends only on the measurement primitive.
--
--   The bound is uniform in the unknown state $\rho$, which is what makes the sample size of Theorem 1 computable in advance.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 11, Lemma 1, (S6); norm (S7), p. 12

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem lemma_1 {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (ρ : Op n) (hρ : WildeQIT.IsDensityOperator ρ)
    (O : Op n) (hO : O.IsHermitian) :
    snapVar E ρ O ≤ shadowNorm E (traceless O) ^ 2 := by sorry
end ClassicalShadow.Linear
