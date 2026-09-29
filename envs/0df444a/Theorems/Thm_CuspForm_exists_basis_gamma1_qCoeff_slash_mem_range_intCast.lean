-- Prove2me | Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
-- name    : CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/7060fa81-fac0-5d1d-b746-2a05b22dfe00
-- title:
--   Integral q-expansion basis for S_k(Γ₁(N))
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be an integer. The assertion is that there exist a natural number $n$ and a basis $b : \mathrm{Fin}\,n \to \mathrm{CuspForm}(\Gamma_1(N), k)$ of the complex vector space of weight-$k$ cusp forms for the congruence subgroup $\Gamma_1(N)$, indexed by $\mathrm{Fin}\,n$, with the following integrality property: for every index $i$, every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(N)$ and every natural number $m$, the quantity $\mathrm{ModularFormClass.qCoeff}\big((b\,i) \mid[k]\,\gamma\big)\,m$ — by definition the $m$-th coefficient of the $q$-expansion of width $1$ (parameter $q = e^{2\pi i \tau}$) of the weight-$k$ slash translate of the underlying function $\mathbb{H} \to \mathbb{C}$ of $b\,i$ by $\gamma$ — belongs to the range of the canonical map $\mathbb{Z} \to \mathbb{C}$, i.e. is a rational integer. The indexing of the basis by a finite type carries with it the finite-dimensionality of $\mathrm{CuspForm}(\Gamma_1(N), k)$; the conclusion asserts membership in $\mathbb{Z}$ of the coefficients of all $\Gamma_0(N)$-translates of each basis element, not the stronger statement that the forms with this property form a $\mathbb{Z}$-lattice spanning the space.
--
--   This is the existence half of the integral structure on $S_k(\Gamma_1(N))$ cut out by $q$-expansions of all $\Gamma_0(N)$-translates (equivalently, of all diamond translates), as in Proposition 2.7 of Deligne–Serre. It is the source of rationality and integrality statements for Hecke eigenvalues used further on, and is cited by the results on primitive forms and on the rational Hecke algebra at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by sorry
