-- Prove2me | Theorems.Thm_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective
-- name    : AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/ca94b5ef-e809-5aae-897d-300f6e872e9c
-- title:
--   Kernel orders multiply along a surjection
-- statement:
--   Let $A$, $B$, $C$ be additive groups (not assumed abelian), let $f \colon A \to B$ and $g \colon B \to C$ be additive group homomorphisms, and assume that $f$ is surjective as a map of underlying sets. Then the natural-number cardinality of the kernel of the composite $g \circ f$ satisfies $$\#\ker(g \circ f) = \#\ker g \cdot \#\ker f,$$ where the three kernels are taken as subgroups of $A$, $B$ and $A$ respectively and $\#$ denotes `Nat.card`, which assigns the value $0$ to an infinite type. Thus for finite kernels this is the expected multiplicativity, and in the infinite cases the identity holds degenerately: if any one of the three kernels is infinite then, under the surjectivity hypothesis, the asserted equation still holds since both sides vanish. No finiteness assumption is imposed anywhere. Surjectivity of $f$ cannot be omitted: for $f = g = 0$ on $\mathbb{Z}/2$ the left-hand side is $2$ while the right-hand side is $4$.
--
--   This is Lagrange's theorem applied to the restriction of $f$ to $\ker(g \circ f)$, and expresses the multiplicativity of the invariant $\beta \mapsto \#\ker\beta$ along surjective homomorphisms. It is used in the computation of the order of the kernel of an endomorphism of a degree-zero divisor class group, in [`AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_natAbs_resultant_of_pushforwardAlong_frobenius`](thm.html#AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_natAbs_resultant_of_pushforwardAlong_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by sorry
