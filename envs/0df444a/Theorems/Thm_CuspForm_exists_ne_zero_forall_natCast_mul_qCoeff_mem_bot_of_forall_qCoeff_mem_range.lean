-- Prove2me | Theorems.Thm_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
-- name    : CuspForm.exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2a75272a-9800-536d-933b-84f8c59992fb
-- title:
--   Bounded denominators for rational cusp forms on Γ_H(M)
-- statement:
--   Fix a natural number $M$ which is nonzero, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a weight $k \in \mathbb{Z}$. Let $\Gamma_H(M)$ be the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism `gamma0Units` sending $\gamma \in \Gamma_0(M)$ to the unit of $\mathbb{Z}/M$ represented by its lower-right entry. Let $f$ be a cusp form of weight $k$ for (the image in $\mathrm{GL}_2(\mathbb{R})$ of) this group, and write $\mathrm{qCoeff}(f)(n)$ for the $n$-th coefficient of the $q$-expansion of $f$ taken with period $1$, i.e. of `UpperHalfPlane.qExpansion 1 f`. Assume that for every $n \in \mathbb{N}$ the coefficient $\mathrm{qCoeff}(f)(n)$ lies in the range of the structure map $\mathbb{Q} \to \mathbb{C}$, that is, is a rational number. The conclusion is that there exists a natural number $D \ne 0$ such that for every $n \in \mathbb{N}$ the product $D \cdot \mathrm{qCoeff}(f)(n)$ lies in the bottom subring $\bot$ of $\mathbb{C}$, i.e. is the image of a rational integer.
--
--   This is the bounded-denominators property for cusp forms with rational Fourier coefficients at $\infty$, transported from $\Gamma_1(M)$ to the intermediate groups $\Gamma_H(M)$, with the denominator bound recorded as a single nonzero natural number $D$ clearing all coefficients simultaneously. It feeds the $p$-local integrality statement [`CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt`](thm.html#CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt), where a form with $\mathbb{Z}_{(p)}$-valued coefficients is made integral after multiplication by an integer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n ∈ (algebraMap ℚ ℂ).range) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, (D : ℂ) * ModularFormClass.qCoeff (⇑f) n ∈ (⊥ : Subring ℂ) := by sorry
