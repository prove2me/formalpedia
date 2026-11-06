-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_7
-- name    : DRSub4633.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:09:22.254102+00:00
-- url     : https://prove2.me/theorems/21d3a7ff-96ab-4fb8-96ca-2292ce28f2b6
-- title:
--   Lemma 4.7 — scalar averaging inequality
-- statement:
--   The weights of (17)–(23) satisfy (20):
--   $$\int_0^1\varpi=\beta=\int_0^1\kappa_0,\quad\int_0^1w=1-\beta,\quad\int_0^1(\lambda+\kappa)=1,\quad\lambda+\kappa=w+\kappa_0,\quad\kappa\ge\kappa_0,\quad\int_t^1\varpi\ge\int_t^1\kappa_0=b(t_0-t)_+,$$
--   with $\beta=bt_0$. The functions $\theta_+$ and $\theta_-$ cross exactly once, at $z\in(3/4,1)$; $\theta$ is absolutely continuous and
--   $$\theta(0)=\Gamma e^{-s}-b,\quad\theta(1)=\Gamma,\quad\theta'(t)=s\theta(t)+b\psi(t)\ \text{a.e.},\quad 0\le\psi\le\rho_1,\quad\int_0^1e^{-st}\psi(t)\,dt=1.\tag{45}$$
--   With $B(\tau)=e^{-s\tau}\int_0^\tau[\theta(t)-\rho_1(t)]e^{st}dt$ (46), for every $0\le\tau\le T\le 1$ and every nonincreasing measurable $q:[\tau,T]\to[1/2,1]$,
--   $$\int_\tau^T\{\Lambda(q(t))W(t)+\mathfrak c(q(t))\lambda(t)-\Gamma\}\,dt\le B(\tau).\tag{47}$$
--   This scalar inequality is where the constant $\Gamma$, and hence $\alpha_0$, is earned.
--
--   Differences from the source:
--   - encoding: the pointwise relations of (20) and (45) → stated for t ∈ [0,1]; reason: the weights are defined on [0,1]; same content
--   - reading: θ+ and θ− cross exactly once, at z → θ+ < θ− on [0, z), θ+(z) = θ−(z), θ+ > θ− on (z, 1]; reason: precise meaning of a single crossing at z
--   - encoding: θ absolutely continuous; θ' identity for a.e. t → AbsolutelyContinuousOnInterval θ 0 1; HasDerivAt a.e. on [0,1]; reason: Mathlib's notions; same content
--   - encoding: nonincreasing measurable q : [τ, T] → [1/2, 1] → q : ℝ → ℝ, AntitoneOn on [τ, T], restriction to [τ, T] measurable, values in [1/2, 1] there; reason: values outside [τ, T] are never used; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.7, p.20

import Mathlib
import Definitions.Def_DRSub4633_Bbudget
import Definitions.Def_DRSub4633_psi
import Definitions.Def_DRSub4633_LamFun
import Definitions.Def_DRSub4633_cFun
import Definitions.Def_DRSub4633_WTail
import Definitions.Def_DRSub4633_lam
import Definitions.Def_DRSub4633_kappa
import Definitions.Def_DRSub4633_kappa0
import Definitions.Def_DRSub4633_varpiDens
import Definitions.Def_DRSub4633_wDens
import Definitions.Def_DRSub4633_t0

namespace DRSub4633

/-- **Lemma 4.7 (Scalar averaging inequality).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.7, p.20: "The weights in
(17)–(23) satisfy (20). The functions `θ₊` and `θ₋` cross exactly once, at `z ∈ (3/4, 1)`; the
function `θ` is absolutely continuous, and [(45)]. Define `B(τ)` (46). Then for every
`0 ≤ τ ≤ T ≤ 1` and every nonincreasing measurable `q : [τ, T] → [1/2, 1]`,
`∫_τ^T {Λ(q(t))W(t) + 𝔠(q(t))λ(t) − Γ} dt ≤ B(τ)`. (47)"

(20), p.12: `∫_0^1 ϖ = β = ∫_0^1 κ₀`, `∫_0^1 w = 1 − β`, `∫_0^1 (λ + κ) = 1`, `λ + κ = w + κ₀`,
`κ ≥ κ₀`, `∫_t^1 ϖ(r) dr ≥ ∫_t^1 κ₀(r) dr = b(t₀ − t)₊`, with `β = bt₀` (17).
(45), p.20: `θ(0) = Γe^(−s) − b`, `θ(1) = Γ`, `θ′(t) = sθ(t) + bψ(t)` for a.e. `t`,
`0 ≤ ψ(t) ≤ ρ₁(t)`, `∫_0^1 e^(−st)ψ(t) dt = 1`.

**Formalization Note.** The pointwise relations of (20) are stated on `[0, 1]`. "Cross exactly once,
at `z`" is: `θ₊ < θ₋` on `[0, z)`, `θ₊(z) = θ₋(z)`, `θ₊ > θ₋` on `(z, 1]`. Absolute continuity is
Mathlib's `AbsolutelyContinuousOnInterval θ 0 1`. "For a.e. `t`" is for Lebesgue measure on
`[0, 1]`. The profile is `q : ℝ → ℝ`, nonincreasing on `[τ, T]` with values in `[1/2, 1]` there, and
measurable on `[τ, T]` (its restriction is measurable). -/
theorem lemma_4_7 :
    -- (20)
    (∫ t in (0 : ℝ)..1, varpiDens t = bPar * t0 ∧ ∫ t in (0 : ℝ)..1, kappa0 t = bPar * t0 ∧
      ∫ t in (0 : ℝ)..1, wDens t = 1 - bPar * t0 ∧ ∫ t in (0 : ℝ)..1, (lam t + kappa t) = 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, lam t + kappa t = wDens t + kappa0 t ∧ kappa0 t ≤ kappa t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ r in t..1, kappa0 r ≤ ∫ r in t..1, varpiDens r ∧
        ∫ r in t..1, kappa0 r = bPar * max (t0 - t) 0)) ∧
    -- single crossing at z ∈ (3/4, 1)
    (3 / 4 < zCross ∧ zCross < 1 ∧ (∀ t ∈ Set.Ico (0 : ℝ) zCross, thetaPlus t < thetaMinus t) ∧
      thetaPlus zCross = thetaMinus zCross ∧
      (∀ t ∈ Set.Ioc zCross 1, thetaMinus t < thetaPlus t)) ∧
    -- θ absolutely continuous and (45)
    AbsolutelyContinuousOnInterval theta 0 1 ∧
    (theta 0 = Gam * Real.exp (-sPar) - bPar ∧ theta 1 = Gam ∧
      (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
        HasDerivAt theta (sPar * theta t + bPar * psi t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ psi t ∧ psi t ≤ rho1 t) ∧
      ∫ t in (0 : ℝ)..1, Real.exp (-(sPar * t)) * psi t = 1) ∧
    -- (47)
    (∀ τ T : ℝ, 0 ≤ τ → τ ≤ T → T ≤ 1 → ∀ q : ℝ → ℝ, AntitoneOn q (Set.Icc τ T) →
      Measurable ((Set.Icc τ T).domRestrict q) →
      (∀ t ∈ Set.Icc τ T, q t ∈ Set.Icc (1 / 2 : ℝ) 1) →
      ∫ t in τ..T, (LamFun (q t) * WTail t + cFun (q t) * lam t - Gam) ≤ Bbudget τ) := by sorry

end DRSub4633
