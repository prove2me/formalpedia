-- Prove2me | Theorems.Thm_ForkJoinDelay_eq_7_base_case
-- name    : ForkJoinDelay.eq_7_base_case
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:16.317196+00:00
-- url     : https://prove2.me/theorems/30cff0a6-a044-4eae-9824-0f8f397de4c8
-- title:
--   Eq. (7) and $Z_{1,1}$ — the base case $\Psi_{0,0,0}$
-- statement:
--   Let $\mu_0,\mu_1,\mu_2>0$ and $w_0,w_{FJ}\in\mathbb C$ with nonnegative real parts. In the fork-join network:
--
--   1. $\Psi_{0,0,0}=Z_{1,1}\,d(0,0)$;
--   2. $d(0,0)=\dfrac{\mu_0}{\mu_0+w_0}$, so $\Psi_{0,0,0}=\dfrac{\mu_0}{\mu_0+w_0}Z_{1,1}$;
--   3. for $t\ge0$, $F_{S_{FJ}|1,1}(t)=(1-e^{-\mu_1t})(1-e^{-\mu_2t})$, the distribution function of the maximum of independent exponentials with rates $\mu_1,\mu_2$;
--   4. $Z_{1,1}=\displaystyle\int_0^\infty e^{-w_{FJ}t}\bigl[\mu_1e^{-\mu_1t}(1-e^{-\mu_2t})+\mu_2e^{-\mu_2t}(1-e^{-\mu_1t})\bigr]dt$;
--   5. $Z_{1,1}=\dfrac{\mu_1}{\mu_1+w_{FJ}}-\dfrac{\mu_1}{\mu_1+\mu_2+w_{FJ}}+\dfrac{\mu_2}{\mu_2+w_{FJ}}-\dfrac{\mu_2}{\mu_1+\mu_2+w_{FJ}}$.
--
--   These give the transform in closed form when the tagged customer finds the whole network empty.
--
--   **Formalization Note** $\Gamma(1,\mu)$ is the exponential law with rate $\mu$, so item 3 is stated for $\Gamma(1,\mu_1)\otimes\Gamma(1,\mu_2)$, the law in $Z_{1,1}$.
--
--   Differences from the source:
--   - encoding: E_{k,h1,h2}[·]: expectation given the state (k, h1, h2) at the tagged customer's arrival → expectation in an explicit FCFS construction from i.i.d. exponential services (residual services included), no arrivals after the tagged customer (IsFJModel, sojournQ0, sojournFJ); reason: the paper's own argument: residual services are exponential by memorylessness (pp.9–10) and later arrivals do not matter (p.8)
--   - reading: FJ stations may be single-, multiple- or infinite-server; 'From here on, we shall assume both stations in the FJ part have a single server' (p.8) → single-server FCFS stations UFJ and LFJ; reason: the paper fixes single servers on p.8 and (2) is the single-server formula
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform arguments w0, wFJ (domain not stated; LST on real w ≥ 0) → complex w0, wFJ with Re w0 ≥ 0, Re wFJ ≥ 0; reason: real w ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - encoding: Z_{x,y}(wFJ) := E[e^{−wFJ SFJ} | h1 = x, h2 = y] = ∫_0^∞ e^{−wFJ t} dF_{SFJ|x,y}(t) (5) → ∫ e^{−wFJ max(s,t)} d(Gamma(x,µ1) ⊗ Gamma(y,µ2)) (boundaryLST); reason: p.12 identifies (S1|h1 = x) ∼ Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2), independent; milestone sec_3_1_fj_cdf connects the two
--   - reading: F_{SFJ|1,1}(t) for t (range not stated) → t ≥ 0; reason: the sojourn time is nonnegative; the printed formula is the distribution function on [0, ∞)
--   - encoding: ∫_0^∞ … dt → Bochner integral over Set.Ioi 0; reason: the integrands are integrable on (0, ∞); same value
--   - encoding: a(r1,r2) defined as an integral (p.10) → a(r1,r2) in the closed form of (4) (coefA); b, c, d the tsums of it; reason: the closed form is proved in (4); milestone eq_4_coefficients states that the two agree
--   - encoding: probabilities P(·) → (P A).toReal for the ENNReal-valued measure; reason: P is a probability measure, so the value is finite; same number
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (7) and the two displays after it, p.13

import Mathlib
import Definitions.Def_ForkJoinDelay_IsFJModel
import Definitions.Def_ForkJoinDelay_psi
import Definitions.Def_ForkJoinDelay_boundaryLST
import Definitions.Def_ForkJoinDelay_coefD

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The base case (7) and the transform `Z_{1,1}`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (7) and the two displays after it, p.13:

1. `Ψ_{0,0,0} = Z_{1,1} d(0,0)`;
2. `d(0,0) = µ₀/(µ₀ + w₀)` (so `Ψ_{0,0,0} = µ₀/(µ₀+w₀) Z_{1,1}`);
3. `F_{S_FJ|1,1}(t) = (1 − e^{−µ₁t})(1 − e^{−µ₂t})` for `t ≥ 0`, the CDF of the maximum of
   independent exponentials with rates `µ₁, µ₂`;
4. `Z_{1,1} = ∫₀^∞ e^{−w_FJ t} (µ₁e^{−µ₁t}(1 − e^{−µ₂t}) + µ₂e^{−µ₂t}(1 − e^{−µ₁t})) dt`;
5. `Z_{1,1} = µ₁/(µ₁+w_FJ) − µ₁/(µ₁+µ₂+w_FJ) + µ₂/(µ₂+w_FJ) − µ₂/(µ₁+µ₂+w_FJ)`.

For positive rates and complex `w₀, w_FJ` with nonnegative real parts.

**Formalization Note.** `Gamma(1, µ)` is Mathlib's `expMeasure µ` (by definition), so item 3 is
stated for `gammaMeasure 1 µ₁ ⊗ gammaMeasure 1 µ₂`, the law in `boundaryLST μ₁ μ₂ 1 1`. -/
theorem eq_7_base_case {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (V U G : ℕ → Ω → ℝ) (hM : IsFJModel P μ₀ μ₁ μ₂ V U G)
    (w₀ wFJ : ℂ) (hw₀ : 0 ≤ w₀.re) (hwFJ : 0 ≤ wFJ.re) :
    psi P V U G 0 0 0 w₀ wFJ = boundaryLST μ₁ μ₂ 1 1 wFJ * coefD μ₀ μ₁ μ₂ w₀ 0 0 ∧
    coefD μ₀ μ₁ μ₂ w₀ 0 0 = (μ₀ : ℂ) / (μ₀ + w₀) ∧
    (∀ t : ℝ, 0 ≤ t →
      (((gammaMeasure 1 μ₁).prod (gammaMeasure 1 μ₂)) {p : ℝ × ℝ | max p.1 p.2 ≤ t}).toReal =
        (1 - Real.exp (-(μ₁ * t))) * (1 - Real.exp (-(μ₂ * t)))) ∧
    boundaryLST μ₁ μ₂ 1 1 wFJ =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(wFJ * t)) *
        ((μ₁ * Real.exp (-(μ₁ * t)) * (1 - Real.exp (-(μ₂ * t))) +
          μ₂ * Real.exp (-(μ₂ * t)) * (1 - Real.exp (-(μ₁ * t))) : ℝ) : ℂ) ∧
    boundaryLST μ₁ μ₂ 1 1 wFJ =
      (μ₁ : ℂ) / (μ₁ + wFJ) - (μ₁ : ℂ) / (μ₁ + μ₂ + wFJ) + (μ₂ : ℂ) / (μ₂ + wFJ) -
        (μ₂ : ℂ) / (μ₁ + μ₂ + wFJ) := by sorry

end ForkJoinDelay
