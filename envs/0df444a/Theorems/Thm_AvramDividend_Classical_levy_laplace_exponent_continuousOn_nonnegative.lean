-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
-- name    : AvramDividend.Classical.levy_laplace_exponent_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:23:13.190639+00:00
-- url     : https://prove2.me/theorems/1fa27b74-bf2c-4549-8110-d30ac84f57e6
-- title:
--   Canonical Lévy Laplace exponent continuous on the full nonnegative ray
-- statement:
--   Under the source canonical spectrally negative Lévy assumptions, the Laplace exponent ψ is continuous on the whole nonnegative half-line. Its Lévy jump integral is continuous on every [0,B] by an integrable compensated-exponential envelope; a source-neutral compact-to-ray gluing lemma yields global continuity. This removes the final continuum assumption from the already Proved positive Esscher-root theorem for unbounded-variation Lévy processes.
-- source:
--   Proved continuousOn_Ici_of_continuousOn_Icc_zero and local Lévy exponent continuity via uniform quadratic Lévy kernel bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_laplace_exponent_continuousOn_nonnegative
 {Ω : Type*} [mΩ : MeasurableSpace Ω]
 {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
 (X : SpectrallyNegativeLevy P 𝓕) :
 ContinuousOn X.ψ (Ici (0 : ℝ)) := by sorry
