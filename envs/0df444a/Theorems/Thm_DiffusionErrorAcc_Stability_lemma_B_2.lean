-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_B_2
-- name    : DiffusionErrorAcc.Stability.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:13.062813+00:00
-- url     : https://prove2.me/theorems/0069b766-e927-462b-8b13-0c838531a346
-- title:
--   Lemma B.2 — square-root Poincaré for posterior statistics: Var_{p_t}(f_t) ≤ e^{−t}√(C_P(p; f)Var_p(f)E_{p_t}‖∇f_t‖²)
-- statement:
--   Let $p$ be the ground-truth law, $p_t$ its Ornstein–Uhlenbeck marginals, $f:\mathbb R^d\to\mathbb R$ a test statistic with $\mathrm{Var}_p(f)>0$, $f_t(y)=\mathbb E[f(Z_0)\mid Z_t=y]$, and $C_P(p;f)\in[0,\infty]$ the f-conditioned Poincaré constant. Then for every $0<t<T$,
--   $$\mathrm{Var}_{p_t}(f_t)\le e^{-t}\sqrt{C_P(p;f)\,\mathrm{Var}_p(f)\,\mathbb E_{p_t}\|\nabla f_t\|^2}.$$
--   The f-conditioned Poincaré inequality at time $0$ propagates to a square-root Poincaré bound for every posterior statistic, with a factor $e^{-t}$; combined with the variance identity it forces exponential variance decay (Lemma B.4).
--
--   **Formalization Note.** Both sides are in `ℝ≥0∞`: the left side is Mathlib's `evariance`, the right side uses `x ^ (1/2 : ℝ)` and the convention $0\cdot\infty=0$.
--
--   Differences from the source:
--   - encoding: p a distribution on ℝ^d with positive C¹ density, p_t = Law(e^{−t}Z_0 + √(1 − e^{−2t})G), ∇log p_t → p = densMeasure ρ with IsRegDensity ρ; p_t = ouMarginal ρ t, the law with the explicit Gaussian-convolution density ouDensity ρ t (ρ at t = 0); ∇log p_t = ouScore ρ t, the gradient of the log of that density; reason: §2.3 makes every distribution have a positive C¹ density; the convolution is the density of e^{−t}Z_0 + √(1 − e^{−2t})G
--   - encoding: f_t(y) := E[f(Z_0) | Z_t = y] for the forward OU process → ouPosterior ρ f t: f at t = 0 and Bayes' formula ∫ f(z)ρ(z)φ_{1−e^{−2t}}(y − e^{−t}z) dz / p_t(y) for t > 0; reason: the continuous version of the conditional expectation, defined at every y
--   - encoding: standing assumptions of §2.1/§2.3: d ≥ 1, T > 0; ∇log p_t Lipschitz in x uniformly in t and continuous in (x, t); the test statistic f uniformly continuous, C² and in L²(p) → explicit hypotheses hd, hT, hscore (IsLipContDrift of (x, t) ↦ ∇log p_t(x) on ℝ^d × [0, T]), hfu, hf2, hfL2; reason: the paper's standing assumptions written as binders, no more
--   - encoding: C_P(p; f) used for a test statistic f (Definition 2.4 requires Var_p(f) > 0) → hypothesis hvar : 0 < Var_p(f); reason: excludes only the case where C_P(p; f) is undefined
--   - encoding: Var_{p_t}(f_t), C_P(p; f) and E_{p_t}‖∇f_t‖² in [0, ∞] read with real arithmetic → computed in ℝ≥0∞ (lintegral, ENNReal.ofReal, x ^ (1/2) for the square root); reason: the energies may be +∞; ℝ≥0∞ avoids the Bochner-integral default value 0 on non-integrable functions
--   - reading: √(C_P(p; f)·Var_p(f)·E_{p_t}‖∇f_t‖²) when C_P(p; f) = ∞ and E_{p_t}‖∇f_t‖² = 0 (∞ · 0, not defined by the source) → 0 (the ℝ≥0∞ convention ∞ · 0 = 0); reason: the only reading under which the printed bound is a statement in that corner
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 24, Lemma B.2

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy
import Definitions.Def_DiffusionErrorAcc_Stability_OUMarginal
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma B.2 (square-root Poincaré for posterior statistics, p. 24). Let `p = ρ dx` (standing
assumptions of §2.1, §2.3) and let `f : ℝ^d → ℝ` be a test statistic with `Var_p(f) > 0`. Then
for every `0 < t < T`,
`Var_{p_t}(f_t) ≤ e^{−t} √(C_P(p; f) Var_p(f) E_{p_t} ‖∇f_t‖²)`, in `[0, ∞]`. -/
theorem lemma_B_2 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (hscore : IsLipContDrift (fun x t => ouScore ρ t x) T)
    (f : Rd d → ℝ) (hfL2 : MemLp f 2 (densMeasure ρ)) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f) (hvar : 0 < variance f (densMeasure ρ)) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      evariance (ouPosterior ρ f t) (ouMarginal ρ t) ≤
        ENNReal.ofReal (Real.exp (-t)) *
          (poincareConstF ρ f * ENNReal.ofReal (variance f (densMeasure ρ)) *
            ∫⁻ y, ‖gradient (ouPosterior ρ f t) y‖ₑ ^ 2 ∂(ouMarginal ρ t)) ^ (1 / 2 : ℝ) := by sorry

end DiffusionErrorAcc.Stability
