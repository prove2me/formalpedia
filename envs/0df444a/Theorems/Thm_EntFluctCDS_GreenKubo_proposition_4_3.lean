-- Prove2me | Theorems.Thm_EntFluctCDS_GreenKubo_proposition_4_3
-- name    : EntFluctCDS.GreenKubo.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:31.160573+00:00
-- url     : https://prove2.me/theorems/344673c2-c9fb-4bc4-983a-abf8230982c6
-- title:
--   Proposition 4.3 — finite-time GES symmetry of the log-Laplace functional
-- statement:
--   Let $(M,\phi_X,\omega_X,\Phi_X)$ be a regular force family satisfying (T1) and (T2). Define $g_t(X,Y)$ as the extended log-Laplace transform of the time-integrated flux under the state $\omega_X$. For every force $X$, test vector $Y$, and real time $t$,
--
--   $$g_t(X,Y)=g_t(X,X-Y).$$
--
--   This functional symmetry is the form of the generalized Evans–Searles relation used in finite-time linear response.
--
--   **Formalization Note** The equality is in extended real numbers, so it also covers infinite exponential moments. Unlike the flux law at zero time, the log-Laplace functional itself is defined at $t=0$.
-- source:
--   Jakšić, Pillet & Rey-Bellet, Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, p. 19, Proposition 4.3, (4.29)

import Mathlib
import Definitions.Def_EntFluctCDS_GreenKubo_Family

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace EntFluctCDS.GreenKubo

/-- Proposition 4.3, p. 19, with extended log-Laplace values. -/
theorem proposition_4_3 {N : ℕ} {M : Type*} [MeasurableSpace M]
    (F : Family N M) (hT1 : T1 F) (hT2 : T2 F) :
    ∀ (X Y : Fin N → ℝ) (t : ℝ),
      gesFunctional F t X Y = gesFunctional F t X (X - Y) := by sorry

end EntFluctCDS.GreenKubo
