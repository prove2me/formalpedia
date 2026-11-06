-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_2
-- name    : DRSub4633.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:07:56.441803+00:00
-- url     : https://prove2.me/theorems/bb9d4a0a-71c3-4e18-8cdd-6beb56e31755
-- title:
--   Lemma A.2 — crossing point
-- statement:
--   The crossing point satisfies
--   $$z>\tfrac34>t_1,$$
--   so $\psi=\rho_1$ on $[0,3/4]$, which contains the ramp, and the identities (45) hold:
--   $$\theta(0)=\Gamma e^{-s}-b,\quad\theta(1)=\Gamma,\quad\theta'(t)=s\theta(t)+b\psi(t)\ \text{for a.e. } t,\quad 0\le\psi(t)\le\rho_1(t),\quad\int_0^1e^{-st}\psi(t)\,dt=1.$$
--
--   Differences from the source:
--   - encoding: θ'(t) = sθ(t) + bψ(t) for a.e. t → for almost every t ∈ [0,1], θ has derivative sθ(t) + bψ(t) at t (HasDerivAt); reason: Lean convention for an a.e. derivative identity; same content
--   - encoding: 0 ≤ ψ(t) ≤ ρ₁(t) → stated for t ∈ [0,1]; reason: the weights are defined on [0,1]; same content
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.2, p.44

import Mathlib
import Definitions.Def_DRSub4633_zCross
import Definitions.Def_DRSub4633_t1
import Definitions.Def_DRSub4633_psi
import Definitions.Def_DRSub4633_theta
import Definitions.Def_DRSub4633_Gam
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_sPar

namespace DRSub4633

/-- **Lemma A.2 (Crossing point).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.2, p.44: "The crossing point `z` satisfies
`z > 3/4 > t₁`, so `ψ = ρ₁` on `[0, 3/4]`, which contains the ramp. The identities (45) hold."
(45), p.20: `θ(0) = Γe^(−s) − b`, `θ(1) = Γ`, `θ′(t) = sθ(t) + bψ(t)` for a.e. `t`,
`0 ≤ ψ(t) ≤ ρ₁(t)`, `∫_0^1 e^(−st)ψ(t) dt = 1`.

**Formalization Note.** "`θ′(t) = sθ(t) + bψ(t)` for a.e. `t`" is: for almost every `t ∈ [0, 1]`,
`θ` is differentiable at `t` with that derivative. `0 ≤ ψ ≤ ρ₁` is on `[0, 1]`. "which contains the
ramp" (`[t₀, t₁] ⊆ [0, 3/4]`) follows from `3/4 > t₁` and is not restated. -/
theorem lemma_A_2 :
    3 / 4 < zCross ∧ t1 < 3 / 4 ∧ (∀ t ∈ Set.Icc (0 : ℝ) (3 / 4), psi t = rho1 t) ∧
    theta 0 = Gam * Real.exp (-sPar) - bPar ∧ theta 1 = Gam ∧
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      HasDerivAt theta (sPar * theta t + bPar * psi t) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ psi t ∧ psi t ≤ rho1 t) ∧
    ∫ t in (0 : ℝ)..1, Real.exp (-(sPar * t)) * psi t = 1 := by sorry

end DRSub4633
