-- Prove2me | Theorems.Thm_Auto_fourier_mem_trigSubmodule
-- name    : Auto.fourier_mem_trigSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:49.25958+00:00
-- url     : https://prove2.me/theorems/c9761d32-970a-488c-ad95-32167c2e6689
-- title:
--   Auto: fourier mem trig Submodule
-- statement:
--   The Auto construction uses the fourier mem trig Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L963-L968
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L963-L968

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.fourier_mem_trigSubmodule (k : ℤ) : fourier k ∈ trigSubmodule := by sorry
