-- Prove2me | Theorems.Thm_DedekindZeta_measurable_mul_right_mixedSpace
-- name    : DedekindZeta.measurable_mul_right_mixedSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:45.101646+00:00
-- url     : https://prove2.me/theorems/4944bcf4-95b8-4659-9b32-349f5f907a09
-- title:
--   Dedekind Zeta: measurable mul right mixed Space
-- statement:
--   Multiplication on the right by a fixed `c` is measurable on the mixed space
--   (componentwise continuous multiplication).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1015-L1017
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1015-L1017

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
open MeasureTheory NumberField.mixedEmbedding

theorem DedekindZeta.measurable_mul_right_mixedSpace (c : mixedEmbedding.mixedSpace K) :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) := by sorry
