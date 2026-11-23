-- Prove2me | Theorems.Thm_DedekindZeta_sum_class_tsum_absNorm
-- name    : DedekindZeta.sum_class_tsum_absNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:43:13.42381+00:00
-- url     : https://prove2.me/theorems/f3d109ad-3bec-47ce-8acb-2ac5b8228c1a
-- title:
--   Dedekind Zeta: sum class tsum abs Norm
-- statement:
--   **Partition over ideal classes**: the finite sum over the class group of the
--   partial Dedekind zetas recovers the full sum over nonzero integral ideals.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1437-L1456
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1437-L1456

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

theorem DedekindZeta.sum_class_tsum_absNorm {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K),
        ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s)
      = ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by sorry
