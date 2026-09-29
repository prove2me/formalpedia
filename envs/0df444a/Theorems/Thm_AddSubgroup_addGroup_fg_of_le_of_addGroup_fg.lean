-- Prove2me | Theorems.Thm_AddSubgroup_addGroup_fg_of_le_of_addGroup_fg
-- name    : AddSubgroup.addGroup_fg_of_le_of_addGroup_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/f0ea6252-d1b1-5dd3-a784-0942d140591d
-- title:
--   Subgroups of finitely generated abelian groups are finitely generated
-- statement:
--   Let $A$ be an additive commutative group (in a fixed universe-zero type) and let $H_1, H_2$ be additive subgroups of $A$ with $H_1 \le H_2$. Assume that the additive group $H_2$, regarded as a type via its coercion, is finitely generated in the sense of Mathlib's `AddGroup.FG`, i.e. there is a finite subset of $H_2$ generating it as an additive group. The conclusion is that $H_1$, likewise regarded as a type, is finitely generated as an additive group. Thus finite generation of additive subgroups of an arbitrary abelian group is inherited by smaller subgroups; no hypothesis of finite generation, torsion-freeness or Noetherianity on the ambient group $A$ is imposed, and no bound relating the number of generators of $H_1$ to that of $H_2$ is asserted.
--
--   This is the standard fact that a subgroup of a finitely generated abelian group is again finitely generated, equivalently the Noetherian property of $\mathbb{Z}$-modules of finite type transported to additive subgroups. It is used in the treatment of the modular Jacobian $J_0$, where finite generation of groups of invariants and the descent step are deduced from finite generation of a larger group, in [`ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le), [`ModularCurve.JZero.addGroup_fg_invariants_rat_of_prime_of_five_le`](thm.html#ModularCurve.JZero.addGroup_fg_invariants_rat_of_prime_of_five_le) and [`ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_addGroup_fg_of_le_of_addGroup_fg.lean

import Mathlib.GroupTheory.Finiteness

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddSubgroup.addGroup_fg_of_le_of_addGroup_fg {A : Type} [AddCommGroup A] {H₁ H₂ : AddSubgroup A}
    (hle : H₁ ≤ H₂) (hfg : AddGroup.FG ↥H₂) : AddGroup.FG ↥H₁ := by sorry
