-- Prove2me | Theorems.Thm_BalancedAlgebra_leftUnit_eq_rightUnit
-- name    : BalancedAlgebra.leftUnit_eq_rightUnit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:34:41.908123+00:00
-- url     : https://prove2.me/theorems/8e12eca3-ae43-4c53-9484-1dc96ba7b1bf
-- title:
--   A left unit composable with a right unit equals it
-- statement:
--   Call $u$ a **left unit** when $u\cdot a=a$ for every $a$ with $u\cdot a$ defined, and $v$ a **right unit** when $a\cdot v=a$ for every $a$ with $a\cdot v$ defined.
--
--   $$u \text{ a left unit},\ v \text{ a right unit},\ u\cdot v \text{ defined}\ \Longrightarrow\ u=v.$$
--
--   This is the manuscript's "key fact about units", and it is what later forces the left and right unit structures of a quivered algebra to coincide. No balance or associativity hypothesis is needed: the product $u\cdot v$ equals $v$ because $u$ is a left unit and equals $u$ because $v$ is a right unit.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §1 (p. 3): "A key fact about units is that if u is a left unit and v is a right unit, then if uv is defined, then u = v."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem leftUnit_eq_rightUnit {A : Type*} (P : PartialAlgebra A) (u v : A)
    (hu : P.IsLeftUnit u) (hv : P.IsRightUnit v) (huv : P.IsDefined u v) : u = v := by sorry

end BalancedAlgebra
