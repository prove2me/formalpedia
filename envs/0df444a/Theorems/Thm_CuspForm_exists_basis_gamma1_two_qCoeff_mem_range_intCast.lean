-- Prove2me | Theorems.Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast
-- name    : CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/08965e61-1661-5c6e-acdb-0d14fd84db16
-- title:
--   Integral basis for weight-two cusp forms on Γ₁(M)
-- statement:
--   Let $M$ be a nonzero natural number. The assertion is that there exist a natural number $n$ and a basis $b$, indexed by `Fin n`, of the complex vector space $\mathrm{CuspForm}(\Gamma_1(M), 2)$ of cusp forms of weight $2$ for the congruence subgroup $\Gamma_1(M)$, with the property that for every index $i$ and every natural number $m$ the quantity $\mathrm{qCoeff}(b_i)(m)$ lies in the range of the canonical map $\mathbb{Z} \to \mathbb{C}$, i.e. is a rational integer. Here, for a function $f : \mathbb{H} \to \mathbb{C}$, the project's $\mathrm{qCoeff}(f)(m)$ is the $m$-th coefficient of the $q$-expansion of $f$ taken with width $1$, that is, the $m$-th Fourier coefficient of $f$ in $q = e^{2\pi i \tau}$ at the cusp $\infty$; the cusp form $b_i$ is used here via its underlying function on the upper half-plane. Since the index type is `Fin n`, the statement incorporates the finite-dimensionality of $\mathrm{CuspForm}(\Gamma_1(M), 2)$ as part of the existence claim. Only the expansion at $\infty$ is constrained; nothing is asserted about the other cusps.
--
--   This is the integral structure on the space of weight-two cusp forms of level $\Gamma_1(M)$: the space is spanned by forms all of whose Fourier coefficients at $\infty$ are rational integers. It is the modular-forms input used downstream to show that the Hecke eigenvalues of a weight-two eigenform generate a finitely generated subring of $\mathbb{C}$, and thence in the comparison of Hecke eigenvalues with Tate-module data on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast (M : ℕ) [NeZero M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℤ → ℂ) := by sorry
