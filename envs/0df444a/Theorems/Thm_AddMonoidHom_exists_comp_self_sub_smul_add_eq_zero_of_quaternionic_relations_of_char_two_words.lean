-- Prove2me | Theorems.Thm_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words
-- name    : AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/f5576832-7758-5dc3-bbe2-61d3d374f7a9
-- title:
--   Quadratic relations for twelve words in σ,i,j
-- statement:
--   Let $V$ be an additive commutative group and let $\sigma, i, j \colon V \to V$ be additive endomorphisms satisfying, pointwise on $V$, the relations $\sigma(\sigma(\sigma T)) = T$, $i(iT) = -T$, $j(jT) = -T$, $i(jT) = -j(iT)$, $\sigma(iT) = j(\sigma T)$, $\sigma(jT) = j(i(\sigma T))$ and $\sigma(\sigma T) + \sigma T + T = 0$. Let $m \colon V \to V$ be an additive endomorphism which is assumed to be one of the twelve composites $\mathrm{id}$, $\sigma$, $\sigma\circ\sigma$, $i$, $i\circ\sigma$, $i\circ(\sigma\circ\sigma)$, $j$, $j\circ\sigma$, $j\circ(\sigma\circ\sigma)$, $i\circ j$, $(i\circ j)\circ\sigma$, $(i\circ j)\circ(\sigma\circ\sigma)$ (the hypothesis is the disjunction of these twelve equalities of additive monoid homomorphisms). The conclusion asserts the existence of an integer $t$ with $t \in \{-1, 0, 1, 2\}$, such that $t = 2$ forces $m = \mathrm{id}$, and such that $m(mT) - t \cdot mT + T = 0$ for every $T \in V$; that is, $m$ satisfies the monic quadratic $m^2 - t\,m + 1 = 0$ as an endomorphism of $V$, with trace $t$ in that four-element set and $t = 2$ only in the trivial case.
--
--   The relations are those satisfied by the automorphisms of a supersingular elliptic curve in characteristic $2$ acting on its points, the automorphism group being of order $24$; the statement extracts from them, for each of the twelve relevant words, a monic quadratic relation with integral trace in $\{-1,0,1,2\}$. It is used by [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two), where such a trace bound is what is needed for the curves with $j = 0$ in characteristic $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.exists_comp_self_sub_smul_add_eq_zero_of_quaternionic_relations_of_char_two_words
    {V : Type*} [AddCommGroup V] (σ i j : V →+ V)
    (hσ3 : ∀ T, σ (σ (σ T)) = T) (hi : ∀ T, i (i T) = -T) (hj : ∀ T, j (j T) = -T)
    (hij : ∀ T, i (j T) = -(j (i T))) (hσi : ∀ T, σ (i T) = j (σ T)) (hσj : ∀ T, σ (j T) = j (i (σ T)))
    (hσ : ∀ T, σ (σ T) + σ T + T = 0)
    (m : V →+ V)
    (hm : m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
        m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
        m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
        m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧ (t = 2 → m = AddMonoidHom.id _) ∧
      ∀ T, m (m T) - t • m T + T = 0 := by sorry
