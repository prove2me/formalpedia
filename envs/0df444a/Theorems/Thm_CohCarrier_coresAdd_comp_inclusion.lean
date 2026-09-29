-- Prove2me | Theorems.Thm_CohCarrier_coresAdd_comp_inclusion
-- name    : CohCarrier.coresAdd_comp_inclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/482a616e-3d3c-52ce-bb2e-33d9a03d919e
-- title:
--   Corestriction of a restricted character is [L:K] times corestriction
-- statement:
--   Let $G$ be a group, $B$ an additive abelian group, and $K \le L$ two subgroups of $G$ (the inclusion being witnessed by `hKL`), with $K$, $L$ and the subgroup $K \cap L$ viewed inside $L$ (that is, `K.subgroupOf L`) all of finite index. Let $\chi \colon \mathrm{Additive}\,L \to B$ be an additive group homomorphism, i.e. a character of $L$ with values in $B$ written additively. Composing $\chi$ with the additivisation of the inclusion $K \hookrightarrow L$ gives the restricted character $\chi|_K \colon \mathrm{Additive}\,K \to B$. The operation `coresAdd` sends a character of a finite-index subgroup to a character of $G$ by transporting it to a homomorphism into $\mathrm{Multiplicative}\,B$, forming the Mathlib transfer map $G \to \mathrm{Multiplicative}\,B$ of that homomorphism, and transporting back. The assertion is the equality of additive homomorphisms $\mathrm{Additive}\,G \to B$
--   $$\mathrm{coresAdd}_K(\chi|_K) \;=\; [L : K]\cdot \mathrm{coresAdd}_L(\chi),$$
--   where $[L:K]$ is the index of `K.subgroupOf L` and the right-hand side is that natural number acting on the homomorphism by scalar multiplication.
--
--   This is the additive form of the transitivity of the transfer (corestriction) combined with the fact that corestriction composed with restriction is multiplication by the index: in degree one with trivial action, $\mathrm{cor}^G_K \circ \mathrm{res}^L_K = [L:K]\,\mathrm{cor}^G_L$. It is used in the comparison of degree maps and Hecke operators at lower level, namely by [`CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower`](thm.html#CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower), its coprime variant, and [`CohCarrier.jDeg_iDeg_four_identities_of_dvd`](thm.html#CohCarrier.jDeg_iDeg_four_identities_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_coresAdd_comp_inclusion.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.coresAdd_comp_inclusion {G : Type*} [Group G] {B : Type*} [AddCommGroup B] (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (χ : Additive ↥L →+ B) :
    coresAdd K (χ.comp (Subgroup.inclusion hKL).toAdditive)
      = (K.subgroupOf L).index • coresAdd L χ := by sorry
