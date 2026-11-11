-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_B_3
-- name    : DiffusionErrorAcc.Stability.lemma_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:14.925215+00:00
-- url     : https://prove2.me/theorems/c93cdccc-eca4-4126-955b-2b990625a0f0
-- title:
--   Lemma B.3 — propagation of realizability: V_t(y) = e^{−t}E[V(Z_0) | Z_t = y] realizes p_t by f_t, with E_{p_t}‖V_t‖² ≤ e^{−2t}E_p‖V‖²
-- statement:
--   Let $p$ be the ground-truth law, $p_t$ its Ornstein–Uhlenbeck marginals and $f_t(y)=\mathbb E[f(Z_0)\mid Z_t=y]$ the posterior statistics. Let $f:\mathbb R^d\to\mathbb R$ be a test statistic with $\mathbb E_pf=0$. If a ($C^1$, $L^2(p)$) vector field $V$ realizes perturbation of $p$ by $f$, then for every $t\in[0,T]$ the field
--   $$V_t(y)=e^{-t}\,\mathbb E[V(Z_0)\mid Z_t=y]$$
--   is $C^1$, realizes perturbation of $p_t$ by $f_t$, and
--   $$\mathbb E_{p_t}\|V_t\|^2\le e^{-2t}\,\mathbb E_p\|V\|^2 .$$
--   A field certifying the transport energy of $f$ at time $0$ thus yields one for $f_t$ at time $t$ with energy smaller by $e^{-2t}$; this is the propagation step behind Lemma B.2.
--
--   **Formalization Note.** Since $\mathbb E_pf=0$ and $\mathbb E_{p_t}f_t=\mathbb E_pf=0$, "realizes perturbation by $f$" is `Realizes ρ V f` and by $f_t$ is `Realizes (ouDensity ρ t) V_t f_t`.
--
--   Differences from the source:
--   - encoding: p a distribution on ℝ^d with positive C¹ density, p_t = Law(e^{−t}Z_0 + √(1 − e^{−2t})G), ∇log p_t → p = densMeasure ρ with IsRegDensity ρ; p_t = ouMarginal ρ t, the law with the explicit Gaussian-convolution density ouDensity ρ t (ρ at t = 0); ∇log p_t = ouScore ρ t, the gradient of the log of that density; reason: §2.3 makes every distribution have a positive C¹ density; the convolution is the density of e^{−t}Z_0 + √(1 − e^{−2t})G
--   - encoding: f_t(y) := E[f(Z_0) | Z_t = y] for the forward OU process → ouPosterior ρ f t: f at t = 0 and Bayes' formula ∫ f(z)ρ(z)φ_{1−e^{−2t}}(y − e^{−t}z) dz / p_t(y) for t > 0; reason: the continuous version of the conditional expectation, defined at every y
--   - encoding: standing assumptions of §2.1/§2.3: d ≥ 1, T > 0; ∇log p_t Lipschitz in x uniformly in t and continuous in (x, t); the test statistic f uniformly continuous, C² and in L²(p) → explicit hypotheses hd, hT, hscore (IsLipContDrift of (x, t) ↦ ∇log p_t(x) on ℝ^d × [0, T]), hfu, hf2, hfL2; reason: the paper's standing assumptions written as binders, no more
--   - reading: t unrestricted in the statement → t ∈ [0, T]; reason: Appendix B defines f_t for t ∈ [0, T] (p. 23)
--   - reading: V realizes perturbation of p by f; V_t realizes perturbation of p_t by f_t → V C¹ and in L²(p) with −∇·(ρV) = fρ pointwise; V_t is C¹ and −∇·(p_t V_t) = f_t p_t pointwise; reason: §2.3 makes every vector field C¹; the raw form −∇·(µV) = gµ equals the centred one because E_p f = 0 = E_{p_t} f_t
--   - encoding: E_{p_t}‖V_t‖² and E_p‖V‖² in [0, ∞] read with real arithmetic → computed in ℝ≥0∞ (lintegral, ENNReal.ofReal, x ^ (1/2) for the square root); reason: the energies may be +∞; ℝ≥0∞ avoids the Bochner-integral default value 0 on non-integrable functions
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 24, Lemma B.3, (B.4)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy
import Definitions.Def_DiffusionErrorAcc_Stability_OUMarginal
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory Set
open scoped ENNReal

namespace DiffusionErrorAcc.Stability

/-- Lemma B.3 (propagation of realizability, p. 24). Let `p = ρ dx` (standing assumptions of
§2.1, §2.3) and let `f : ℝ^d → ℝ` be a test statistic with `E_p f = 0`. If the (`C¹`, `L²(p)`)
vector field `V` realizes perturbation of `p` by `f`, then for every `t ∈ [0, T]` the field
`V_t(y) = e^{−t} E[V(Z_0) | Z_t = y]` (a `C¹` field) realizes perturbation of `p_t` by `f_t`, and
`E_{p_t} ‖V_t‖² ≤ e^{−2t} E_p ‖V‖²`. -/
theorem lemma_B_3 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (hscore : IsLipContDrift (fun x t => ouScore ρ t x) T)
    (f : Rd d → ℝ) (hfL2 : MemLp f 2 (densMeasure ρ)) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f) (hmean : ∫ x, f x ∂(densMeasure ρ) = 0)
    (V : Rd d → Rd d) (hV1 : ContDiff ℝ 1 V) (hVL2 : MemLp V 2 (densMeasure ρ))
    (hV : Realizes ρ V f) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ContDiff ℝ 1 (fun y => Real.exp (-t) • ouPosterior ρ V t y) ∧
      Realizes (ouDensity ρ t) (fun y => Real.exp (-t) • ouPosterior ρ V t y)
        (ouPosterior ρ f t) ∧
      ∫⁻ y, ‖Real.exp (-t) • ouPosterior ρ V t y‖ₑ ^ 2 ∂(ouMarginal ρ t) ≤
        ENNReal.ofReal (Real.exp (-2 * t)) * ∫⁻ x, ‖V x‖ₑ ^ 2 ∂(densMeasure ρ) := by sorry

end DiffusionErrorAcc.Stability
