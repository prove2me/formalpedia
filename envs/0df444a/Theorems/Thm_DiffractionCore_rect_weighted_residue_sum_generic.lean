-- Prove2me | Theorems.Thm_DiffractionCore_rect_weighted_residue_sum_generic
-- name    : DiffractionCore.rect_weighted_residue_sum_generic
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:07.09727+00:00
-- url     : https://prove2.me/theorems/0d603aa7-8db0-489c-82a7-3f04990563a9
-- title:
--   Weighted residue sum in a rectangle
-- statement:
--   Let $\sigma_0\le\sigma_1$ and $T_0\le T_1$, and let $S$ be a finite set strictly
--   inside the corresponding rectangle $R$. Let $m:S\to\mathbb Z$ and let $g$ be
--   holomorphic on an open neighborhood of $R$. Then the positively oriented side
--   integrals satisfy
--   $$\int_{\partial R}\sum_{\rho\in S}\frac{m(\rho)g(z)}{z-\rho}\,dz
--   =2\pi i\sum_{\rho\in S}m(\rho)g(\rho).$$
--   The finite sum allows termwise use of the single-pole formula.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/DiffractionCore.lean#L158-L258

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_DiffractionCore_rect_weighted_pole_generic
/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/






open Complex MeasureTheory Real
open scoped Topology

section
namespace DiffractionCore
end DiffractionCore
open DiffractionCore

theorem DiffractionCore.rect_weighted_residue_sum_generic
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    {s : Finset ℂ} (m : ℂ → ℤ) {U : Set ℂ} (g : ℂ → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
    (hin : ∀ ρ ∈ s, sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹))
      - (∫ x in sigma0..sigma1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹))
      + I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹))
      - I • (∫ y in T0..T1, ∑ ρ ∈ s, (m ρ : ℂ)
        * (g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹))
    = 2 * ↑π * I * ∑ ρ ∈ s, (m ρ : ℂ) * g ρ := by sorry
