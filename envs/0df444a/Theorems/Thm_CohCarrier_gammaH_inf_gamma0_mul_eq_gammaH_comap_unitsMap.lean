-- Prove2me | Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
-- name    : CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/2e542850-8d34-5ae9-9ce4-026d965cd765
-- title:
--   Γ_H(M)∩Γ₀(Mℓ)=Γ_{H'}(Mℓ) for H' the unit preimage
-- statement:
--   Let $M$ and $\ell$ be nonzero natural numbers and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$. For a modulus $N$ and a subgroup $K \le (\mathbb{Z}/N)^\times$, the project's $\Gamma_K(N)$ — [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) — is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pushing forward along the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ the preimage of $K$ under the homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121), which sends $\gamma \in \Gamma_0(N)$ to the unit of $\mathbb{Z}/N$ with value the reduction of the lower-right entry $\gamma_{11}$ (its inverse being the reduction of $\gamma_{00}$); concretely, $\Gamma_K(N) = \{A \in \mathrm{SL}_2(\mathbb{Z}) : A \in \Gamma_0(N),\ (A_{11} \bmod N) \in K\}$. The assertion is the equality of subgroups of $\mathrm{SL}_2(\mathbb{Z})$
--   $$\Gamma_H(M) \cap \Gamma_0(M\ell) = \Gamma_{H'}(M\ell),$$
--   where $H' =$ the preimage of $H$ under the reduction homomorphism on units $\mathbb{Z}\mathrm{Mod.unitsMap}$ attached to the divisibility $M \mid M\ell$, i.e. $(\mathbb{Z}/M\ell)^\times \to (\mathbb{Z}/M)^\times$.
--
--   This is the standard compatibility of the groups $\Gamma_H$ under raising the level by a factor $\ell$: intersecting $\Gamma_H(M)$ with $\Gamma_0(M\ell)$ again produces a group of $\Gamma_H$ type, for the pullback of $H$ along unit reduction. It is the transport lemma that lets the level-$\Gamma_H$ machinery (modular curves $X_H$, their function fields, places and Hecke correspondences) be applied to the top curve of the degree-$\ell$ Hecke correspondence on $X_H(M)$, and is cited in the Shapiro-type induction step and in the computations with Hecke operators and diamond operators on $X_1$-type curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) =
      CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by sorry
