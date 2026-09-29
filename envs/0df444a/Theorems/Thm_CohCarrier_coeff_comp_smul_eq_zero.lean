-- Prove2me | Theorems.Thm_CohCarrier_coeff_comp_smul_eq_zero
-- name    : CohCarrier.coeff_comp_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/474a7bef-60a0-5190-94b5-f24daef8c309
-- title:
--   Pushforward along g kills varpi·φ
-- statement:
--   Fix a natural number $M$ and a subgroup $H$ of $(\mathbb{Z}/M)^{\times}$, and let $\Gamma_H(M)$ denote the subgroup `GammaH M H` of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pulling $H$ back along the reduction map `gamma0Units M` on $\Gamma_0(M)$ and pushing the result forward along the inclusion of $\Gamma_0(M)$ into $\mathrm{SL}_2(\mathbb{Z})$. Let $A$ and $B$ be additive abelian groups, let $R$ be a semiring acting on $A$ by a module structure, let $g : A \to B$ be an additive homomorphism and let $\varpi \in R$, and assume that $g(\varpi \cdot a) = 0$ for every $a \in A$. Then for every $\varphi$ in $H^1(M,H;A) := \mathrm{Hom}(\Gamma_H(M)^{\mathrm{add}}, A)$, the group $\Gamma_H(M)$ being written additively so that this group of additive homomorphisms carries the pointwise $R$-module structure, the composite of $\varpi \cdot \varphi$ with $g$ is the zero homomorphism from $\Gamma_H(M)^{\mathrm{add}}$ to $B$.
--
--   A bookkeeping lemma about the coefficient modules $H^1(M,H;A) = \mathrm{Hom}(\Gamma_H(M), A)$ used in the project's model of the cohomology of modular curves: pushing forward along a coefficient map $g$ annihilates the image of multiplication by $\varpi$ whenever $g$ itself annihilates $\varpi A$. It is cited in the construction producing a maximal ideal of the Hecke algebra attached to a class with absolutely irreducible, non-parabolic associated representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_coeff_comp_smul_eq_zero.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.coeff_comp_smul_eq_zero (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {R : Type*} [Semiring R] [Module R A] (g : A →+ B) (ϖ : R)
    (hg : ∀ a : A, g (ϖ • a) = 0) (φ : H1 M H A) :
    g.comp (ϖ • φ) = 0 := by sorry
