-- Prove2me | Theorems.Thm_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure
-- name    : AlgebraicClosure.nonempty_algHom_rat_padicAlgClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/24257173-8689-5f64-bf89-ab3eed3ceaba
-- title:
--   Embedding ℚ̄ into mathbb Qₚ̄ over ℚ
-- statement:
--   For a natural number $p$ that is prime, the type of $\mathbb Q$-algebra homomorphisms from `AlgebraicClosure ℚ` to `AlgebraicClosure ℚ_[p]` is nonempty: that is, there exists a ring homomorphism $\overline{\mathbb Q} \to \overline{\mathbb Q_p}$ commuting with the $\mathbb Q$-algebra structures on the two fields, where $\overline{\mathbb Q}$ is Mathlib's chosen algebraic closure of the rationals and $\overline{\mathbb Q_p}$ is Mathlib's chosen algebraic closure of the field $\mathbb Q_p$ of $p$-adic numbers (whose $\mathbb Q$-algebra structure comes from $\mathbb Q \to \mathbb Q_p \to \overline{\mathbb Q_p}$). Since $\overline{\mathbb Q}$ is a field and the map is a ring homomorphism of fields, any such homomorphism is automatically injective, so the assertion is the existence of an embedding of $\overline{\mathbb Q}$ into $\overline{\mathbb Q_p}$ over $\mathbb Q$. The statement asserts mere nonemptiness; no specific embedding is singled out, and no uniqueness or compatibility with further structure is claimed.
--
--   This is the standard fact that an algebraic closure of $\mathbb Q$ may be realised inside an algebraic closure of $\mathbb Q_p$, allowing algebraic numbers to be viewed $p$-adically. It is used in [`WeierstrassCurve.exists_withConv_equiv_torsionBy_padicAlgClosure_of_ratAlgClosure`](thm.html#WeierstrassCurve.exists_withConv_equiv_torsionBy_padicAlgClosure_of_ratAlgClosure), which transports torsion modules of a Weierstrass curve from the rational algebraic closure to the $p$-adic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicClosure.nonempty_algHom_rat_padicAlgClosure (p : ℕ) [Fact p.Prime] :
    Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) := by sorry
