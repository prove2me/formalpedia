-- Prove2me | Theorems.Thm_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast
-- name    : CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/d96b7864-3b3a-545a-ba9a-75e99825de43
-- title:
--   Rational basis of cusp forms on Γ_H(N)
-- statement:
--   Let $N$ be a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/N\mathbb{Z})^\times$ and $k$ an integer. Write $\Gamma_H(N)$ for the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) that sends $\gamma \in \Gamma_0(N)$ to the unit of $\mathbb{Z}/N\mathbb{Z}$ with value the reduction of the lower right entry of $\gamma$ and inverse the reduction of its upper left entry; thus $\Gamma_H(N) = \{\gamma \in \Gamma_0(N) : d(\gamma) \bmod N \in H\}$. The assertion is that, for the corresponding subgroup of $\mathrm{GL}_2(\mathbb{R})$, there are a natural number $n$ and a $\mathbb{C}$-basis $b$ indexed by `Fin n` of the space `CuspForm` of cusp forms of weight $k$ for $\Gamma_H(N)$ such that for every index $i$ and every natural number $m$ the $m$-th coefficient [`ModularFormClass.qCoeff (b i) m`](def/FLTPrelim_Modularity.html#L19) of the $q$-expansion of period $1$ of $b\,i$ lies in the range of the coercion $\mathbb{Q} \to \mathbb{C}$. In particular the space is finite-dimensional, and it is spanned by cusp forms whose Fourier coefficients at $\infty$ are all rational.
--
--   This is the rational structure of the space of cusp forms for the intermediate groups $\Gamma_1(N) \le \Gamma_H(N) \le \Gamma_0(N)$ (Shimura, Theorem 3.52); the case $H$ trivial is [`CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`](thm.html#CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast), and the passage to general $H$ uses the rationality of $q$-expansions under slashing by elements of $\Gamma_0(N)$ recorded in [`ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0`](thm.html#ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0). It is used in the construction of a $q$-expansion with coefficients in a base-changed Laurent setting, via [`ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range`](thm.html#ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ
      (CuspForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) := by sorry
