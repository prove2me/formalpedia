-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_B_5
-- name    : DiffusionErrorAcc.Stability.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:17.255522+00:00
-- url     : https://prove2.me/theorems/62d0dfab-c253-4392-a69e-d7e2039e4a16
-- title:
--   Lemma B.5 — horizon-free Dirichlet integral ∫_0^T √(E_{p_t}‖∇f_t‖²) dt ≤ 2√((1 + log C)Var_p(f)), C = max(C_P(p; f), 1)
-- statement:
--   Let $p$ be the ground-truth law, $p_t$ its Ornstein–Uhlenbeck marginals, $f:\mathbb R^d\to\mathbb R$ a test statistic with $\mathrm{Var}_p(f)>0$, $f_t(y)=\mathbb E[f(Z_0)\mid Z_t=y]$, and $C=\max(C_P(p;f),1)$. Then
--   $$\int_0^T\sqrt{\mathbb E_{p_t}\|\nabla f_t\|^2}\,dt\le2\sqrt{(1+\log C)\,\mathrm{Var}_p(f)}.$$
--   The bound does not depend on the horizon $T$; inserted into the adjoint estimate (Lemma A.1) it gives Theorem B.1.
--
--   **Formalization Note.** The left side is a lower Lebesgue integral in `ℝ≥0∞` over $(0,T)$; $\log$ is the natural logarithm; the statement assumes $C_P(p;f)<\infty$.
--
--   Differences from the source:
--   - encoding: p a distribution on ℝ^d with positive C¹ density, p_t = Law(e^{−t}Z_0 + √(1 − e^{−2t})G), ∇log p_t → p = densMeasure ρ with IsRegDensity ρ; p_t = ouMarginal ρ t, the law with the explicit Gaussian-convolution density ouDensity ρ t (ρ at t = 0); ∇log p_t = ouScore ρ t, the gradient of the log of that density; reason: §2.3 makes every distribution have a positive C¹ density; the convolution is the density of e^{−t}Z_0 + √(1 − e^{−2t})G
--   - encoding: f_t(y) := E[f(Z_0) | Z_t = y] for the forward OU process → ouPosterior ρ f t: f at t = 0 and Bayes' formula ∫ f(z)ρ(z)φ_{1−e^{−2t}}(y − e^{−t}z) dz / p_t(y) for t > 0; reason: the continuous version of the conditional expectation, defined at every y
--   - encoding: standing assumptions of §2.1/§2.3: d ≥ 1, T > 0; ∇log p_t Lipschitz in x uniformly in t and continuous in (x, t); the test statistic f uniformly continuous, C² and in L²(p) → explicit hypotheses hd, hT, hscore (IsLipContDrift of (x, t) ↦ ∇log p_t(x) on ℝ^d × [0, T]), hfu, hf2, hfL2; reason: the paper's standing assumptions written as binders, no more
--   - encoding: C_P(p; f) used for a test statistic f (Definition 2.4 requires Var_p(f) > 0) → hypothesis hvar : 0 < Var_p(f); reason: excludes only the case where C_P(p; f) is undefined
--   - encoding: C = max(C_P(p; f), 1) ∈ [1, ∞] → hypothesis C_P(p; f) ≠ ∞ and C = max(C_P(p; f).toReal, 1) ∈ ℝ; reason: when C_P(p; f) = ∞ the right side is +∞ (Var_p(f) > 0) and the inequality is trivial; only that case is excluded
--   - encoding: the time integral ∫_0^T √(E_{p_t}‖∇f_t‖²) dt in [0, ∞] read with real arithmetic → computed in ℝ≥0∞ (lintegral, ENNReal.ofReal, x ^ (1/2) for the square root); reason: the energies may be +∞; ℝ≥0∞ avoids the Bochner-integral default value 0 on non-integrable functions
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 26, Lemma B.5

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy
import Definitions.Def_DiffusionErrorAcc_Stability_OUMarginal
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma B.5 (p. 26). Let `p = ρ dx` (standing assumptions of §2.1, §2.3) and let `f : ℝ^d → ℝ`
be a test statistic with `Var_p(f) > 0`. Write `C := max(C_P(p; f), 1)`. Then
`∫_0^T √(E_{p_t} ‖∇f_t‖²) dt ≤ 2 √((1 + log C) Var_p(f))`. Stated for `C_P(p; f) < ∞` (otherwise
the right side is `+∞`). -/
theorem lemma_B_5 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (hscore : IsLipContDrift (fun x t => ouScore ρ t x) T)
    (f : Rd d → ℝ) (hfL2 : MemLp f 2 (densMeasure ρ)) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f) (hvar : 0 < variance f (densMeasure ρ))
    (hCfin : poincareConstF ρ f ≠ ∞) :
    ∫⁻ t in Ioo (0 : ℝ) T,
        (∫⁻ y, ‖gradient (ouPosterior ρ f t) y‖ₑ ^ 2 ∂(ouMarginal ρ t)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.sqrt ((1 + Real.log (max (poincareConstF ρ f).toReal 1)) *
        variance f (densMeasure ρ))) := by sorry

end DiffusionErrorAcc.Stability
