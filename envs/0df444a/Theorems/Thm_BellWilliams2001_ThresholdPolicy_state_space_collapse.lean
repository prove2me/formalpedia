-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_state_space_collapse
-- name    : BellWilliams2001.ThresholdPolicy.state_space_collapse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:34:45.337889+00:00
-- url     : https://prove2.me/theorems/4fa6574f-6862-48e0-b5c0-ec31c1f6f3d0
-- title:
--   Theorem 5.2 — state-space collapse: $(\hat Q_1^r,\hat Q_2^r,\hat I_1^r,\hat I_2^r)\Rightarrow(0,\tilde Q_2^*,0,\tilde I_2^*)$
-- statement:
--   There is a constant $c_0>0$, depending only on the model data, such that if the $r$-th system operates under the threshold policy $T^{r,*}$ of Definition 5.1 with $c>c_0$, then
--   $$(\hat Q_1^r,\hat Q_2^r,\hat I_1^r,\hat I_2^r)\Longrightarrow(\mathbf 0,\tilde Q_2^*,\mathbf 0,\tilde I_2^*)\qquad\text{as }r\to\infty,$$
--   where $\tilde Q_2^*=y_2^{-1}\tilde W^*$ is a one-dimensional reflected Brownian motion started from zero with drift $(\mu_3/\mu_2)\theta_1+\theta_2$ and variance parameter $(\mu_3/\mu_2)^2(\lambda_1\alpha_1^2+\mu_1\beta_1^2+(\lambda_1-\mu_1)\beta_2^2)+\lambda_2(\alpha_2^2+\beta_3^2)$, and $\tilde I_2^*=\mu_2^{-1}\tilde V^*$ is a multiple of its local time at the origin, both as in (41)–(42).
--
--   Under the threshold policy the two-dimensional queue collapses onto the class 2 axis, and its diffusion limit is the optimally controlled Brownian system; Theorem 5.3's convergence of costs is derived from it.
--
--   **Formalization Note** The limit is built from an arbitrary pair of independent standard Brownian motions (the statement holds for each such pair). Weak convergence in $\mathbf D^4$ to a limit with continuous paths is stated in coupling form: there are copies with the same laws (of the paths on $[0,\infty)$, for all large $r$) on one probability space, with Skorokhod paths, converging uniformly on compact time intervals almost surely; this is equivalent by the Skorokhod representation theorem in one direction and because a.s. u.o.c. convergence implies weak convergence in the other. The threshold relations are required only for the systems with $L^r\ge1$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 622, Theorem 5.2; p. 620, (41)–(42)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory
open scoped NNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Theorem 5.2 (p. 622), state-space collapse. There is `c₀ > 0` (depending only on the model
data) such that under the threshold policies of Definition 5.1 with any `c > c₀` (required for
the systems with `L^r ≥ 1`), `(Q̂^r_1, Q̂^r_2, Î^r_1, Î^r_2) ⟹ (0, Q̃*_2, 0, Ĩ*_2)`, where
`Q̃*_2 = y₂^{-1} W̃*` and `Ĩ*_2 = μ₂^{-1} Ṽ*` are given by (41)–(42) from the two-dimensional
Brownian motion `X̃` (drift `θ`, covariance `diag(σ₁², σ₂²)`), here built from an arbitrary pair
of independent standard Brownian motions. The weak convergence in `D⁴` to a limit with
continuous paths is stated in its coupling form (`CouplingConverges`). -/
theorem state_space_collapse {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ),
        IsBrownianPair P' B →
        CouplingConverges M.P P'
          (fun n ω t => ![M.Qhat n (Tstar n) ω t 0, M.Qhat n (Tstar n) ω t 1,
            M.Ihat n (Tstar n) ω t 0, M.Ihat n (Tstar n) ω t 1])
          (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]) := by sorry

end BellWilliams2001.ThresholdPolicy
