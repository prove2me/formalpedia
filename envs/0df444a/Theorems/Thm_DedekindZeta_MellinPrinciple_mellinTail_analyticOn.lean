-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_analyticOn
-- name    : DedekindZeta.MellinPrinciple.mellinTail_analyticOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:22:08.954445+00:00
-- url     : https://prove2.me/theorems/8e735872-b6ec-48ea-864c-e66f90999f52
-- title:
--   Mellin Principle: mellin Tail analytic On
-- statement:
--   **The tail `F(s)` is entire.**
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L308-L336
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L308-L336

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.mellinTail_analyticOn (h : IsMellinPair f g a₀ b₀ C k c α) :
    AnalyticOnNhd ℂ (mellinTail f g a₀ b₀ C k) Set.univ := by sorry
