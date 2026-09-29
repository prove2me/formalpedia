-- Prove2me | Theorems.Thm_CohCarrier_coresAdd_comp_subtype
-- name    : CohCarrier.coresAdd_comp_subtype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/b988064d-9bcf-517c-96ba-32f8c610fa6b
-- title:
--   Corestriction of a restricted additive character is [G:K]·φ
-- statement:
--   Let $G$ be a group, $K \le G$ a subgroup of finite index, and $B$ an additive abelian group; let $\varphi : \mathrm{Additive}\,G \to B$ be an additive group homomorphism, i.e. a homomorphism from $G$ written additively to $B$. Restrict $\varphi$ along the additivised inclusion $\mathrm{Additive}\,K \to \mathrm{Additive}\,G$, obtaining $\varphi \circ \iota : \mathrm{Additive}\,K \to B$, and apply `coresAdd K` to it; by definition `coresAdd K` is the group-theoretic transfer `MonoidHom.transfer` for the finite-index subgroup $K$ and the abelian target, conjugated by the equivalences between additive and multiplicative notation, so it sends a homomorphism $\mathrm{Additive}\,K \to B$ to a homomorphism $\mathrm{Additive}\,G \to B$. The assertion is the equality of homomorphisms $\mathrm{Additive}\,G \to B$
--   $$\mathrm{coresAdd}_K(\varphi \circ \iota) = [G:K] \cdot \varphi,$$
--   where $[G:K]$ is `Subgroup.index` and $\cdot$ is the natural-number scalar multiplication on homomorphisms, i.e. $g \mapsto [G:K]\,\varphi(g)$ for all $g \in G$.
--
--   This is the composite $\mathrm{cor} \circ \mathrm{res} = [G:K]$ of group cohomology in degree one with trivial action, where the corestriction is the transfer, stated for additively written characters. It supplies the diagonal terms of the degeneracy/trace computations for homomorphism groups of congruence subgroups, and is used in the results on Hecke operators and Eisenstein classes in the same development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_coresAdd_comp_subtype.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.coresAdd_comp_subtype {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive G →+ B) :
    coresAdd K (φ.comp (Subgroup.subtype K).toAdditive) = K.index • φ := by sorry
