-- Prove2me | Theorems.Thm_CuspForm_stableD
-- name    : CuspForm.stableD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b8b93024-341b-5916-af1c-aea0d5085174
-- title:
--   Diamond slashes of Γ_H(M) cusp forms vanish at cusps
-- statement:
--   Let $M$ be a positive natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ and let $k$ be an integer. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(M)\hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ of the preimage under `gamma0Units M` of $H$ (so: the matrices of $\Gamma_0(M)$ whose associated unit mod $M$ lies in $H$), and regard it as a subgroup of $\mathrm{GL}(2,\mathbb{R})$ via `Matrix.SpecialLinearGroup.mapGL`. The theorem asserts the proposition [`CuspForm.StableD M H k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72), which unfolds to the following statement: for every $\sigma\in\Gamma_0(M)$, every cusp form $f$ of weight $k$ for $\Gamma_H(M)$, and every point $c$ of the one-point compactification `OnePoint ℝ` of the real line, if $c$ is a cusp of $\Gamma_H(M)$ viewed inside $\mathrm{GL}(2,\mathbb{R})$, then the weight-$k$ slash $f\mid[k]\,\sigma$, formed using the image of $\sigma$ in $\mathrm{GL}(2,\mathbb{R})$, is zero at $c$ in the sense of `OnePoint.IsZeroAt`.
--
--   This is the cusp-vanishing input required to define the diamond operators on cusp forms for $\Gamma_H(M)$: since $\Gamma_H(M)$ is normal in $\Gamma_0(M)$ only up to the relevant slash action, one must know that slashing a cusp form by an element of $\Gamma_0(M)$ again satisfies the vanishing conditions at all cusps. It is the hypothesis discharged for the construction of the diamond and Hecke operators on $\Gamma_H(M)$-cusp forms, and is used throughout the Eichler–Shimura and eigenform arguments built on that construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_stableD.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.stableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by sorry
