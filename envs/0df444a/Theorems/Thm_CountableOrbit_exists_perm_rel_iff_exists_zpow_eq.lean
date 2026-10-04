-- Prove2me | Theorems.Thm_CountableOrbit_exists_perm_rel_iff_exists_zpow_eq
-- name    : CountableOrbit.exists_perm_rel_iff_exists_zpow_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T19:30:29.582567+00:00
-- url     : https://prove2.me/theorems/506d353f-577e-4bdb-825b-42df371db067
-- title:
--   Every equivalence relation with countable classes is the orbit relation of one permutation
-- statement:
--   Let $r$ be an equivalence relation on a set $X$ whose classes are countable. Then there is a bijection $T$ of $X$ such that $x \mathrel r y$ if and only if $y = T^n(x)$ for some $n \in \mathbb Z$: arrange each class as a finite cycle or as a copy of $\mathbb Z$.
--
--   Lodha and Moore define (p. 4): "Let $X$ be a Polish space and let $E \subseteq X^2$ be an equivalence relation which is Borel and which has countable equivalence classes. $E$ is $\mu$-amenable if, after discarding a $\mu$-measure $0$ set, $E$ is the orbit equivalence relation of an action of $\mathbb Z$." The definition does not say that the action of $\mathbb Z$ is Borel. Read without that, this theorem makes every such relation $\mu$-amenable, and Theorem 2.2 would be false; Theorem 2.2 says the orbit relation of a countable dense subgroup of $\mathrm{PSL}_2(\mathbb R)$ on the projective line is not amenable with respect to Lebesgue measure. The Lodha–Moore mission's definition (`LodhaMoore.IsMuAmenable`) takes the action to be by a Borel automorphism.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, the definition of a μ-amenable relation read without "Borel" for the action of ℤ

import Mathlib

namespace CountableOrbit

theorem exists_perm_rel_iff_exists_zpow_eq {X : Type*} (r : X → X → Prop) (hr : Equivalence r)
    (hc : ∀ x, {y | r x y}.Countable) :
    ∃ T : Equiv.Perm X, ∀ x y, r x y ↔ ∃ n : ℤ, (T ^ n) x = y := by
  sorry

end CountableOrbit
