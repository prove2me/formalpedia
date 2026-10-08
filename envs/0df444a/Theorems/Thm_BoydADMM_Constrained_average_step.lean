-- Prove2me | Theorems.Thm_BoydADMM_Constrained_average_step
-- name    : BoydADMM.Constrained.average_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:20:15.886217+00:00
-- url     : https://prove2.me/theorems/19abd7e2-acfa-40f3-ae45-653241bdb925
-- title:
--   The parallel-projection dual average vanishes in one step
-- statement:
--   Let $N\ge1$, $\rho>0$, let $\mathcal A_i\subseteq\mathbb R^n$ be nonempty closed convex sets, and let $(x^k,z^k,u^k)$ be any parallel projection ADMM run from arbitrary $z^0,u^0$. Averaging its second and third updates gives, for every $k\ge0$,
--
--   $$z^{k+1}=\bar x^{k+1}+\bar u^k,\qquad \bar u^{k+1}=0.$$
--
--   The identities explain when the common iterate equals the average and provide the index base for the simplified algorithm.
--
--   **Formalization Note** The book prints $-z^k$ in the intermediate averaged dual update; the displayed iteration on page 35 and the next line on page 36 require $-z^{k+1}$. This statement uses the corrected index.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 36, §5.1.2, averaged updates; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_BoydADMM_Constrained_Run

namespace BoydADMM.Constrained

/-- §5.1.2, p. 36: averaging the last two updates eliminates the dual average. -/
theorem average_step {N n : ℕ} (hN : 0 < N) (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (ρ : ℝ) (hρ : 0 < ρ)
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n)
    (hrun : IsParallelRun A x z u) :
    ∀ k, z (k + 1) = avg (x (k + 1)) + avg (u k) ∧ avg (u (k + 1)) = 0 := by sorry

end BoydADMM.Constrained
