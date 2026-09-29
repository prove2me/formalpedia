-- Prove2me | Theorems.Thm_CommGroup_index_range_powMonoidHom_eq_pow_finrank
-- name    : CommGroup.index_range_powMonoidHom_eq_pow_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/f3681c54-40ae-5612-bdcf-c58ceb6a2fa0
-- title:
--   Index of n-th powers in a finitely generated torsion-free abelian group
-- statement:
--   Let $F$ be a commutative group, written multiplicatively, which is finitely generated as a group. Assume $F$ is torsion-free in the elementary sense that for every $x \in F$ and every natural number $m > 0$, $x^m = 1$ forces $x = 1$. Let $n$ be a natural number with $n > 0$. Then the subgroup $\mathrm{range}(\mathtt{powMonoidHom}\ n)$, the image of the $n$-th power endomorphism $x \mapsto x^n$ of $F$, that is the subgroup $F^n$ of $n$-th powers, has index in $F$ equal to $n^{r}$, where $r = \operatorname{finrank}_{\mathbb{Z}} (\mathrm{Additive}\ F)$ is the rank of $F$ regarded as a $\mathbb{Z}$-module via its additive copy. Here the index is the Mathlib notion `Subgroup.index`, the cardinality of the coset space as a natural number (so the assertion in particular records that this index is finite).
--
--   This is the standard computation $[F : F^n] = n^{\operatorname{rank} F}$ for a finitely generated torsion-free abelian group. It is used in the count of $S$-units modulo $n$-th powers, being cited by [`NumberField.natCard_sUnit_quotient_range_powMonoidHom`](thm.html#NumberField.natCard_sUnit_quotient_range_powMonoidHom); the torsion-freeness hypothesis is phrased elementarily so that subgroups of multiplicative groups of fields, and quotients by torsion, can be fed to it directly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommGroup_index_range_powMonoidHom_eq_pow_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CommGroup.index_range_powMonoidHom_eq_pow_finrank {F : Type*} [CommGroup F] [Group.FG F]
    (htf : ∀ (x : F) (m : ℕ), 0 < m → x ^ m = 1 → x = 1) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : F →* F).range.index = n ^ Module.finrank ℤ (Additive F) := by sorry
