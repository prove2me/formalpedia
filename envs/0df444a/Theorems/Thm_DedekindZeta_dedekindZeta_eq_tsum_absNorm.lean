-- Prove2me | Theorems.Thm_DedekindZeta_dedekindZeta_eq_tsum_absNorm
-- name    : DedekindZeta.dedekindZeta_eq_tsum_absNorm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:43:00.64098+00:00
-- url     : https://prove2.me/theorems/9d6ac125-d20a-465c-a8d6-574f8e7039ff
-- title:
--   Dedekind Zeta: dedekind Zeta eq tsum abs Norm
-- statement:
--   The Dedekind Zeta construction uses the dedekind Zeta eq tsum abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L57-L203
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L57-L203

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

theorem DedekindZeta.dedekindZeta_eq_tsum_absNorm {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by sorry
