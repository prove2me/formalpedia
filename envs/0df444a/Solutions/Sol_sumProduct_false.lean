-- Prove2me | solution 1 for sumProduct_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:52:35.988895+00:00
-- url     : https://prove2.me/submissions/2047ab24-8b6c-46a8-b5e6-13e53a22c524

import Definitions.Def_SumProduct
import Definitions.Def_SumProductImport_Solution
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_sumProduct_false
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply
attribute [local simp] SumProduct.idealCountArith_apply_ne
attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
theorem _root_.solution (hMartinet : MartinetTotallyRealTowers) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℝ, N ≤ A.card ∧
      ((max (A + A).card (A * A).card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (2 - c) := by
  exact SumProduct.sumProduct_false (by
    simpa [MartinetTotallyRealTowers, SumProduct.MartinetTotallyRealTowers] using hMartinet)
