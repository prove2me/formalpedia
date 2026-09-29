-- Prove2me | Theorems.Thm_CerednikDrinfeld_classSetForget_mk_of_le
-- name    : CerednikDrinfeld.classSetForget_mk_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/2cdd5c16-2a73-5b3b-b713-053b8605710a
-- title:
--   Forgetful class-set map computed on idelic representatives
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and write $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$ for the associated quaternion algebra, and $\widehat{\mathbb{H}}=\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},\mathrm{fin}}$ for its base change to the finite adele ring of $\mathbb{Q}$ (formed with respect to the ring of integers of $\mathbb{Q}$). Let $U\le U'$ be two subgroups of the unit group $\widehat{\mathbb{H}}^{\times}$, with $h$ witnessing the inclusion $U\le U'$, and let $x\in\widehat{\mathbb{H}}^{\times}$. For a subgroup $V\le\widehat{\mathbb{H}}^{\times}$, `ClassSet V` denotes the double coset quotient of $\widehat{\mathbb{H}}^{\times}$ by the image of the monoid homomorphism [`Submodule.finiteIdeleDiagonal`](def/Submodule_FiniteAdeleBox.html#L43), i.e. the group $\mathbb{H}^{\times}$ embedded through $d\mapsto d\otimes 1$, acting on the left, and by $V$ acting on the right; `ClassSet.mk V x` is the class of $x$. The map [`CerednikDrinfeld.classSetForget U U'`](def/CerednikDrinfeld_ClassSetGraph.html#L18) is defined by choosing, for a class in `ClassSet U`, its canonical representative and taking the class of that representative in `ClassSet U'`. The assertion is that this map sends the class of $x$ modulo $(\mathbb{H}^{\times},U)$ to the class of the same element $x$ modulo $(\mathbb{H}^{\times},U')$.
--
--   This identifies the degeneracy (forgetful) map between the class sets $\mathbb{H}^{\times}\backslash\widehat{\mathbb{H}}^{\times}/U \to \mathbb{H}^{\times}\backslash\widehat{\mathbb{H}}^{\times}/U'$ attached to a shrinking of the level, showing that the definition through chosen representatives agrees with the naive formula on explicit idelic representatives. It is used in the comparison of vertex and edge class sets with the quotient graph in the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_classSetForget_mk_of_le.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.classSetForget_mk_of_le
    {a b : ℚ} {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetForget U U' (QuaternionAlgebra.ClassSet.mk U x) = QuaternionAlgebra.ClassSet.mk U' x := by sorry
