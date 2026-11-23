-- Prove2me | Theorems.Thm_DedekindZeta_mixedEmbedding_norm_eq_absNorm_span_local
-- name    : DedekindZeta.mixedEmbedding_norm_eq_absNorm_span_local
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:45:40.324808+00:00
-- url     : https://prove2.me/theorems/d2d1be8b-43d9-4854-850c-07cc673f7d64
-- title:
--   Dedekind Zeta: mixed Embedding norm eq abs Norm span local
-- statement:
--   **Norm identity** (the standard treatment, local replica of
--   `DedekindZeta.GammaIntegral.mixedEmbedding_norm_eq_absNorm_span`, which lives
--   downstream and is therefore not importable here): the archimedean Minkowski norm
--   of `σ b` equals the absolute norm of the principal ideal `(b)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2160-L2164
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2160-L2164

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
variable {K}

theorem DedekindZeta.mixedEmbedding_norm_eq_absNorm_span_local (b : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K ((b : 𝓞 K) : K))
      = (Ideal.absNorm (Ideal.span {b}) : ℝ) := by sorry
