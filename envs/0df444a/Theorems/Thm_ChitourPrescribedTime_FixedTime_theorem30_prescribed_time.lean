-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_theorem30_prescribed_time
-- name    : ChitourPrescribedTime.FixedTime.theorem30_prescribed_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:10:57.991598+00:00
-- url     : https://prove2.me/theorems/385f72d2-2081-4c4e-80ea-3a7c913566bf
-- title:
--   Theorem 30 — prescribed-time stabilization of the pure chain by the rescaled feedback $\omega^H_{\kappa(D_\lambda x)}(D^{\mathbf r}_\lambda x)$
-- statement:
--   Let $n\ge1$ and let the gains $\ell_1,\dots,\ell_n>0$ and the constant $C>0$ satisfy the decay inequality (36). Then there exist $m\in(0,1)$ and $\kappa_0\in(0,\tfrac1{2n})$, with $r(m,\kappa_0)>0$ and $r(m,-\kappa_0)>0$, such that the following holds. For every prescribed time $T>0$ and every $\lambda>0$ with
--   $$\lambda\ \ge\ \frac{T^\ast(m,\kappa_0)}{T},$$
--   where $T^\ast(m,\kappa_0)$ is the right-hand side of (52), the feedback
--   $$u=\omega^H_{\kappa(D^{\mathbf r}_\lambda x)}\big(D^{\mathbf r}_\lambda x\big),\qquad D^{\mathbf r}_\lambda=\operatorname{diag}(\lambda^{n-i+1})_{i=1}^n,$$
--   renders the pure chain of integrators $\dot x=J_nx+u\,e_n$ globally fixed-time stable at the origin with settling time at most $T$.
--
--   Thus every trajectory of the closed loop reaches the origin by the prescribed time $T$, whatever its initial condition, and the rescaling factor needed is explicit in terms of the parameters of Theorem 28.
--
--   **Formalization Note** The page writes $\kappa_0\in(0,1/n)$ in Theorem 30 while referring to $\kappa_0$ "defined in Theorem 28", where $\kappa_0\in(0,\tfrac1{2n})$; the latter is used. The dilation is that of (5), with weights $n-i+1$, not the dilation $D^{\mathbf r(\kappa)}$ of Proposition 24. The page's "$T(m,\kappa_0)$ defined in (52)" is taken as the right-hand side of (52). The gains and $C$ are data satisfying (36), as in Theorem 28.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1038, Theorem 30

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov
import Definitions.Def_ChitourPrescribedTime_FixedTime_VaryingDegree

namespace ChitourPrescribedTime.FixedTime

/-- Theorem 30 (p. 1038). Let the gains `ℓ` and the constant `C > 0` satisfy (36). There are
`m ∈ (0, 1)` and `κ₀ ∈ (0, 1/(2n))` (as in Theorem 28) with `r(m, ±κ₀) > 0` such that for every
`T > 0` and every `λ > 0` with `λ ≥ T(m, κ₀)/T` (`T(m, κ₀)` the right-hand side of (52)), the
feedback `u = ω^H_{κ(D^r_λ x)}(D^r_λ x)` renders the pure chain (31) globally fixed-time stable at
the origin with settling time at most `T`. -/
theorem theorem30_prescribed_time (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin n → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (C : ℝ) (hC : 0 < C) (h36 : Decay36 ℓ C) :
    ∃ m ∈ Set.Ioo (0 : ℝ) 1, ∃ κ0 ∈ Set.Ioo (0 : ℝ) (1 / (2 * (n : ℝ))),
      0 < rPlus ℓ m κ0 ∧ 0 < rMinus ℓ m κ0 ∧
      ∀ T : ℝ, 0 < T → ∀ lam : ℝ, 0 < lam → settlingBound ℓ C m κ0 ≤ lam * T →
        GloballyFixedTimeStable
          (fun (_ : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
            chainField n x (omegaH ℓ (kappaOf ℓ m κ0 (dilR n lam x)) (dilR n lam x))) T := by sorry

end ChitourPrescribedTime.FixedTime
