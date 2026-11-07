-- Prove2me | Theorems.Thm_CritWinSpin_lemma_4_3
-- name    : CritWinSpin.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:32.481233+00:00
-- url     : https://prove2.me/theorems/ef3ac46e-fde0-4e86-812e-8825cccb38c9
-- title:
--   Lemma 4.3, pp.15–16 — Hessian bounds, second moments and $\mathrm{TV}(\nu_\alpha,q)$, Lipschitz $K_z$
-- statement:
--   There are $M_0,C_K>0$ depending only on $\rho$ such that for all $N$, $L$ with $LL^\top\preceq sI_N$, $\tau<s\le2\tau+1$, $\alpha\in(0,1]$ and $h\in\mathbb R^N$:
--
--   1. for a.e. $z$, $0\preceq\nabla^2W(z)\preceq I_N$ and $\alpha I_N\preceq\nabla^2U_\alpha(z)\preceq(1+\alpha)I_N$;
--   2. with $q\propto e^{-W}$ and $\nu_\alpha\propto e^{-U_\alpha}$,
--   $$\max\{\mathbb E_q\|Z\|^2,\mathbb E_{\nu_\alpha}\|Z\|^2\}\le M_0N,\qquad\mathrm{TV}(\nu_\alpha,q)\le\frac{\alpha M_0N}{2};$$
--   3. for all $z,w$, $\mathrm{TV}(K_z,K_w)\le C_K\sqrt N\|z-w\|$.
--
--   These are the inputs to the Langevin analysis of the sampler.
--
--   Differences from the source:
--   - encoding: ∇²W(z) at a.e. z → the second Fréchet derivative, with its existence at a.e. z a conclusion, as a quadratic form; reason: the Hessian as a form; W is C¹ with a piecewise-C² profile
--   - encoding: expectations and TV of densities → Bochner integrals of normalised densities with Integrable conclusions, TV = ½∫|f − g|; reason: rules out junk values of the integral
--   - reading: constants depending only on ρ → ∃ M₀, C_K before N, L, s, α, h; reason: §3, p.10, and the lemma's wording
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 4.3, pp.15–16, eq. (23)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Wpot
open MeasureTheory IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 4.3** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, pp.15–16). If
`LLᵀ ⪯ s I_N`, `τ < s ≤ 2τ + 1`, `α ∈ (0, 1]`, there are `M₀, C_K > 0` depending only on `ρ` such that for
all `h`: (i) for a.e. `z`, `0 ⪯ ∇²W ⪯ I_N` and `α I_N ⪯ ∇²U_α ⪯ (1 + α) I_N`; (ii) the second moments under
`q ∝ e^{−W}` and `ν_α ∝ e^{−U_α}` are at most `M₀N` and `TV(ν_α, q) ≤ αM₀N/2`, eq. (23);
(iii) `TV(K_z, K_w) ≤ C_K √N ‖z − w‖`. -/
theorem lemma_4_3 (S : SpinLaw) (hS : IsGHS S) :
    ∃ M₀ Cₖ : ℝ, 0 < M₀ ∧ 0 < Cₖ ∧
      ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (s α : ℝ) (h : Fin N → ℝ),
        tau S < s → s ≤ 2 * tau S + 1 →
        (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef →
        0 < α → α ≤ 1 →
        (∀ᵐ z : Fin N → ℝ,
          DifferentiableAt ℝ (fderiv ℝ (Wpot S s L h)) z ∧
          DifferentiableAt ℝ (fderiv ℝ (Ualpha S s α L h)) z ∧
          ∀ v : Fin N → ℝ,
            0 ≤ fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ≤ normSq v ∧
            α * normSq v ≤ fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ≤ (1 + α) * normSq v) ∧
        (Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s α L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Ualpha S s α L h z)) ∧
          max (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z)
              (∫ z : Fin N → ℝ, normSq z * normDens (Ualpha S s α L h) z) ≤ M₀ * (N : ℝ) ∧
          (1 / 2) * (∫ z : Fin N → ℝ,
              |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z|) ≤
            α * M₀ * (N : ℝ) / 2) ∧
        (∀ z w : Fin N → ℝ,
          tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
            Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w))) := by sorry

end CritWinSpin
