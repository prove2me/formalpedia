-- Prove2me | Theorems.Thm_DedekindZeta_tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
-- name    : DedekindZeta.tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:45:34.787745+00:00
-- url     : https://prove2.me/theorems/99365451-a7b5-4d51-b2ea-5c7fbdd5fcdd
-- title:
--   Dedekind Zeta: tsum cone lintegral enorm eq mul tsum orbit
-- statement:
--   **Free-orbit collapse for the fractional cone theta dominating series.**
--   The per-element series over the nonzero
--   `a ∈ I` of cone `enorm`-`lintegral`s of the shifted Gaussian Mellin integrand
--   `g(y·σ a)·N(y)^t` collapses to the base whole-space Gaussian Mellin
--   `enorm`-`lintegral` `M` times an *orbit-indexed* norm-power series.
--
--   The acting group `G = Multiplicative (Fin (rank K) → ℤ)` acts on
--   `S = {a : K // a ∈ I ∧ a ≠ 0}` by multiplication through `coneUnitHom`
--   (`coneFracSMul`), and this action is free (`coneUnitHom` is injective via
--   `coneUnitHom_mem_torsion_iff`, and `a ≠ 0`). For an orbit representative `a₀`,
--   summing the per-element cone-lintegral over the orbit equals (via
--   `mixedEmbedding.unitSMul_smul` + `map_mul` rewriting each `a = coneUnitHom g • a₀`
--   to the helper-4 summand, then `tsum_unit_lintegral_enorm_cone_eq_lintegral_whole`)
--   the whole-space value, which by `lintegral_enorm_mixedGaussian_mul_norm_cpow_eq`
--   is `ofReal (N(σ a₀)^{-Re t}) · M`. Reassembling over the free `G`-orbits
--   (`MulAction` orbit decomposition of `∑' a : S`) factors out `M`. Each orbit term
--   is `ofReal (N(σ a₀)^{-Re t})` for an orbit representative `a₀ ∈ I`, `a₀ ≠ 0`, and
--   the orbit index injects into the nonzero principal fractional ideals `⊆ I`, as
--   required by the downstream finiteness conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1974-L2092
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1974-L2092

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

theorem DedekindZeta.tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = (∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K))
        * ∑' o : Quotient (MulAction.orbitRel
              (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
              {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
            ENNReal.ofReal
              (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by sorry
