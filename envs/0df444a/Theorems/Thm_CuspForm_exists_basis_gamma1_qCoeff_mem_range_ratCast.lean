-- Prove2me | Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
-- name    : CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/92e55786-1c95-5517-90d4-9b2ee51de1c3
-- title:
--   A rational q-expansion basis for S_k(Γ₁(N))
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be an integer. The assertion is that there exist a natural number $n$ and a basis $b : \mathrm{Fin}\,n \to \mathrm{CuspForm}(\Gamma_1(N), k)$ of the complex vector space of cusp forms of weight $k$ for the congruence subgroup $\Gamma_1(N)$, indexed by $\mathrm{Fin}\,n$ (so in particular the space is finite-dimensional of dimension $n$), such that for every index $i$ and every natural number $m$ the quantity $\mathtt{qCoeff}(b\,i)\,m$ lies in the image of the coercion $\mathbb{Q} \to \mathbb{C}$, i.e. is a rational number. Here $\mathtt{qCoeff}\,f\,m$ is by definition the $m$-th coefficient of the $q$-expansion of $f$ of period $1$, that is, the $m$-th Fourier coefficient of $f$ at the cusp $\infty$ with respect to $q = e^{2\pi i \tau}$. Thus $S_k(\Gamma_1(N))$ admits a $\mathbb{C}$-basis all of whose members have rational Fourier coefficients at $\infty$.
--
--   This is the rationality half of the classical arithmetic structure theorem for $S_k(\Gamma_1(N))$ (Shimura's Theorem 3.52 in the field case, and part of the Deligne–Serre rationality statements); it is obtained from the corresponding statement with coefficients in $\mathbb{Q}(e^{2\pi i/N})$ by averaging over the Galois action on $q$-expansions furnished by [`CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply`](thm.html#CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply). It feeds the variant with integral $q$-expansions of all slashes, the analogous statement for the groups $\Gamma_H$, and the comparison of cusp forms with regular differentials on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) := by sorry
