-- Prove2me | Theorems.Thm_AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
-- name    : AddMonoidHom.mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/5feb3dcf-e7cd-55f2-b9e9-ac341eb426e8
-- title:
--   Counting criterion for surjectivity onto q-torsion
-- statement:
--   Let $T$ and $J$ be additive commutative groups, let $f : T \to J$ be an additive homomorphism and let $q$ be an integer such that $q \cdot t = 0$ for every $t \in T$. Assume $T$ is finite and that the subtype $\{x \in J : q \cdot x = 0\}$ is finite. Let $X, Y$ be natural numbers with $Y > 0$ and suppose the two inequalities $\#(\ker f) \cdot X \le \#T \cdot Y$ and $\#\{x \in J : q \cdot x = 0\} \cdot Y \le X$ hold, the cardinalities being `Nat.card`. The conclusion is that every $x \in J$ with $q \cdot x = 0$ lies in the range of $f$; that is, $f$ maps $T$ onto the $q$-torsion subgroup of $J$ (the reverse inclusion being automatic from $qT = 0$). The auxiliary natural numbers $X$ and $Y$ serve only as slack, allowing a user to combine separately obtained bounds without performing divisions.
--
--   An elementary counting criterion: the first isomorphism theorem together with Lagrange's theorem forces an injection of finite sets to be a bijection. It is used in the verification that a torsion map out of a finite $q$-torsion group hits all of the $q$-torsion of the target, for the semistable-curve torsion count cited by [`AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le
    {T J : Type*} [AddCommGroup T] [AddCommGroup J] (f : T →+ J) (q : ℤ) (hT : ∀ t : T, q • t = 0)
    [Finite T] (hfinJ : Finite {x : J // q • x = 0}) (X Y : ℕ) (hY : 0 < Y)
    (hker : Nat.card f.ker * X ≤ Nat.card T * Y) (hJ : Nat.card {x : J // q • x = 0} * Y ≤ X) :
    ∀ x : J, q • x = 0 → x ∈ f.range := by sorry
