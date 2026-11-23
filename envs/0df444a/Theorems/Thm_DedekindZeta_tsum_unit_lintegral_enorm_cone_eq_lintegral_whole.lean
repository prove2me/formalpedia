-- Prove2me | Theorems.Thm_DedekindZeta_tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
-- name    : DedekindZeta.tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:37.778989+00:00
-- url     : https://prove2.me/theorems/3d519cf5-f4dc-4d3e-bf61-39c3c38522b6
-- title:
--   Dedekind Zeta: tsum unit lintegral enorm cone eq lintegral whole
-- statement:
--   **Unit-orbit cone → whole-space collapse** for the shifted Gaussian Mellin
--   `enorm` integrand (helper 3). For any `a : K`
--   and `t : ℂ`, summing the fundamental-cone `enorm`-`lintegral` of the
--   `g`-argument shifted along the `(𝓞 K)ˣ`-orbit (the cone-action group
--   `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)`) over the whole group collapses to the
--   whole-space `enorm`-`lintegral`:
--
--       ∑' g, ∫⁻ x in C, ‖g((g • x)·σ a)·N(x)^t‖ₑ d^*x
--         = ∫⁻ x, ‖g(x·σ a)·N(x)^t‖ₑ d^*x.
--
--   This is `IsFundamentalDomain.lintegral_eq_tsum` for
--   `isFundamentalDomain_fundamentalCone` applied to the nonnegative integrand
--   `y ↦ ‖g(y·σ a)·N(y)^t‖ₑ`, using that the unit action is measure-preserving
--   (`measurePreserving_unitSMul`) and norm-1 (so `N(g • x) = N x`, which is why the
--   norm-power factor reads `N(x)^t` rather than `N(g • x)^t`). The orbit shift is
--   written with the global unit action `coneUnitHom g • y` (equal to the cone action
--   `g • y` by `coneSMul_def`), since the cone `MulAction` instance is section-local.
--   Stated in the
--   cone-indicator `enorm`-`lintegral` form that the assembly child consumes.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1888-L1922
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1888-L1922

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
    (a : K) (t : ℂ) :
    (∑' g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K a) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by sorry
