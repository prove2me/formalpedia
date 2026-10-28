-- Prove2me | Theorems.Thm_DiffractionCore_rect_weighted_pole_generic
-- name    : DiffractionCore.rect_weighted_pole_generic
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:48:16.212673+00:00
-- url     : https://prove2.me/theorems/db2d7eea-ae12-4d41-a563-2d9dc2acea39
-- title:
--   Weighted Cauchy integral for one pole in a rectangle
-- statement:
--   Let $R=[\sigma_0,\sigma_1]\times[T_0,T_1]$ be a complex rectangle, let $\rho$
--   lie strictly inside it, and let $g$ be holomorphic on an open neighborhood of $R$.
--   With the positively oriented boundary integral written as the four oriented side
--   integrals, one has
--   $$\int_{\partial R}\frac{g(z)}{z-\rho}\,dz=2\pi i\,g(\rho).$$
--   This is the single-pole identity used in the rectangle argument principle.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/DiffractionCore.lean#L47-L156

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_RHInBoxAnalytic_rect_winding_generic
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

theorem DiffractionCore.rect_weighted_pole_generic
    (sigma0 sigma1 T0 T1 : ℝ) (ρ : ℂ) {U : Set ℂ} (g : ℂ → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hsub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U)
    (hre0 : sigma0 < ρ.re) (hre1 : ρ.re < sigma1)
    (him0 : T0 < ρ.im) (him1 : ρ.im < T1) :
    (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I * g ρ := by sorry
