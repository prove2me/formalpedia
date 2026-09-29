-- Prove2me | Theorems.Thm_CuspForm_stableT
-- name    : CuspForm.stableT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/cba01703-e4bc-544a-b3dd-0e3afe45a0ff
-- title:
--   Stability of the Γ_H Hecke operator T_ℓ on cusp forms
-- statement:
--   Let $M$ be a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, $k$ an integer and $\ell$ a prime not dividing $M$. The theorem asserts the predicate [`CuspForm.StableT M H k ℓ`](def/CuspForm_HeckeOperatorFormsGammaH.html#L85), which unfolds as follows. Let $\rho$ be an element of $\Gamma_0(M)$ whose $(1,1)$ entry reduces, modulo $M$, to the class of $\ell$, and let $f$ be a cusp form of weight $k$ for the group $\Gamma_H(M)$, namely the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling $H$ back along the map $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ and pushing forward along the inclusion of $\Gamma_0(M)$, regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$. Form the function $$g \;=\; \sum_{j<\ell} f\big|_k \,\mathrm{heckeMatrix}\ \ell\ j \;+\; f\big|_k\bigl(\rho\cdot \mathrm{diag}(\ell,1)\bigr),$$ the first summand being [`ModularForm.heckeU k ℓ f`](def/ModularForm_HeckeOperator.html#L93) and $\mathrm{diag}(\ell,1)$ being [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21), the upper triangular invertible real matrix `upperTriangularGL ℓ 0 1`. Then three statements hold: $g\mid_k\gamma = g$ for every $\gamma$ in $\Gamma_H(M)$ inside $\mathrm{GL}(2,\mathbb{R})$; $g$ is holomorphic on the upper half-plane, in the sense of `MDifferentiable` for the standard complex model; and $g$ is zero at $c$ in weight $k$ for every point $c$ of $\mathbb{R}\cup\{\infty\}$ that is a cusp of $\Gamma_H(M)$.
--
--   This is the classical fact that the weight-$k$ Hecke operator $T_\ell$ at a prime $\ell\nmid M$, written with its diamond-twisted last coset representative $\rho\,\mathrm{diag}(\ell,1)$, maps $S_k(\Gamma_H(M))$ into itself. It discharges the stability input required to define the operator $T_\ell$ on cusp forms for $\Gamma_H(M)$, and is used downstream in the Eichler–Shimura comparison and in the construction of Hecke eigenforms from cohomology classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_stableT.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.stableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by sorry
