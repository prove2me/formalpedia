-- Prove2me | Theorems.Thm_DedekindZeta_summable_absNorm_neg_cpow
-- name    : DedekindZeta.summable_absNorm_neg_cpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:20.931098+00:00
-- url     : https://prove2.me/theorems/5d032d21-e3f2-4200-86c6-7eaa3209a614
-- title:
--   Dedekind Zeta: summable abs Norm neg cpow
-- statement:
--   **Absolute summability** of `𝔞 ↦ 𝔑(𝔞)^{-s}` over the nonzero integral ideals
--   for `1 < s.re`. This is the convergence underlying `dedekindZeta_eq_tsum_absNorm`
--   (the standard treatment): the analytic input is the big-O bound on the ideal-counting
--   partial sums together with `LSeriesSummable_of_sum_norm_bigO_and_nonneg`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1331-L1433
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1331-L1433

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

theorem DedekindZeta.summable_absNorm_neg_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun 𝔞 : NonzeroIdeal K => (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by sorry
