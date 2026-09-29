-- Prove2me | Theorems.Thm_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
-- name    : DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/69cac0c8-5104-54c5-84cb-e07c444d5fe6
-- title:
--   Fibres of the refinement map Γbackslash G/V → Ubackslash G/V
-- statement:
--   Let $G$ be a group, let $\Gamma$ and $U$ be subgroups of $G$ with $\Gamma \le U$, let $V$ be a further subgroup of $G$, and let $\beta \in G$. Consider the double-coset space $\Gamma\backslash G/V$, that is Mathlib's `DoubleCoset.Quotient` of $G$ by the underlying sets of $\Gamma$ and $V$, and inside it the subtype of those classes $q$ for which there exists $g \in G$ whose $(\Gamma,V)$-double coset is $q$ and whose $(U,V)$-double coset equals that of $\beta$; this is the fibre over $U\beta V$ of the natural map $\Gamma\backslash G/V \to U\backslash G/V$. The assertion is that the natural-number cardinality of this fibre equals the natural-number cardinality of the double-coset space of the group $U$ by the two subgroups $\Gamma \cap U$ and $U \cap \beta V \beta^{-1} \cap U$ of $U$, both realised via `Subgroup.subgroupOf`, the conjugate $\beta V \beta^{-1}$ being the image of $V$ under the automorphism $x \mapsto \beta x \beta^{-1}$; since $\Gamma \le U$, the first of these is $\Gamma$ viewed inside $U$, so the right-hand side is $\#\bigl(\Gamma\backslash U/(U \cap \beta V\beta^{-1})\bigr)$. The equality is one of `Nat.card` values, hence reads $0 = 0$ when both sides are infinite.
--
--   This is the standard fibre count for a refinement of double-coset decompositions, as used in Eichler's theory of optimal embeddings (with $G$ an adelic unit group, $U$ and $\Gamma$ global and adelic unit groups of a subfield, and $V$ an adelic order unit group). Here it serves as the group-theoretic bookkeeping behind the count of double cosets for congruence subgroups in [`ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq`](thm.html#ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
    {G : Type*} [Group G] {Γ U : Subgroup G} (V : Subgroup G) (hΓU : Γ ≤ U) (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
          (((U ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf U : Subgroup U) : Set U)) := by sorry
