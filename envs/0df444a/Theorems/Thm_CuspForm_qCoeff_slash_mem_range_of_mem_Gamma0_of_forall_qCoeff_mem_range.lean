-- Prove2me | Theorems.Thm_CuspForm_qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range
-- name    : CuspForm.qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/aa44a86c-7034-55c6-a924-4d038c54b7b7
-- title:
--   Slashing by Γ₀(M) preserves rational q-expansions
-- statement:
--   Fix $M \in \mathbb{N}$, nonzero, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^\times$ and a weight $k \in \mathbb{Z}$. Let $\Gamma_H(M)$ denote the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) $\colon \Gamma_0(M) \to (\mathbb{Z}/M\mathbb{Z})^\times$ whose value on $\gamma$ is the reduction modulo $M$ of the lower right entry of $\gamma$ (with inverse the reduction of the upper left entry); thus $\Gamma_H(M) = \{\gamma \in \Gamma_0(M) : d(\gamma) \bmod M \in H\}$. Let $g$ be a cusp form of weight $k$ for the image of $\Gamma_H(M)$ in $\mathrm{GL}_2(\mathbb{R})$, and assume that for every $n \in \mathbb{N}$ the coefficient [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) $(g)(n)$ — the $n$-th coefficient of the $q$-expansion of $g$ with period $1$ — lies in the range of $\mathbb{Q} \to \mathbb{C}$, i.e. is rational. Let $\rho \in \mathrm{SL}_2(\mathbb{Z})$ with $\rho \in \Gamma_0(M)$. The conclusion is that for every $n \in \mathbb{N}$ the $n$-th $q$-expansion coefficient of the weight-$k$ slash $g \mid[k]\ \rho$, the image of $\rho$ in $\mathrm{GL}_2(\mathbb{R})$ being used, is again rational.
--
--   Since $\rho \in \Gamma_0(M)$ normalises $\Gamma_H(M)$, the slash $g \mid[k]\ \rho$ is the action of the diamond operator $\langle d \rangle$ attached to the lower right entry $d$ of $\rho$ modulo $M$; the statement is the rationality of $q$-expansions at $\infty$ under this action. It feeds the analysis of the rational structure on the two-cusp integral set, being used by [`CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range`](thm.html#CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.qCoeff_slash_mem_range_of_mem_Gamma0_of_forall_qCoeff_mem_range
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range)
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ CongruenceSubgroup.Gamma0 M) :
    ∀ n : ℕ, ModularFormClass.qCoeff
        ((⇑g) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) n ∈ (algebraMap ℚ ℂ).range := by sorry
