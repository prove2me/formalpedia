-- Prove2me | Theorems.Thm_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle
-- name    : Coalgebra.eq_lTensor_comul_sub_tmul_one_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/4b607558-48be-5053-aaea-89319b2b3762
-- title:
--   Cofree comodules: every 1-cocycle in (N⊗ L)⊗ L is a coboundary
-- statement:
--   Let $R$ be a commutative ring, let $L$ be a commutative ring carrying an $R$-bialgebra structure, with comultiplication $\Delta =$ `Coalgebra.comul` and counit $\varepsilon =$ `Coalgebra.counit`, and let $N$ be an $R$-module. Let $e \in (N \otimes_R L) \otimes_R L$, and write $m := (\mathrm{id}_N \otimes \varepsilon \otimes \mathrm{id}_L)(e) \in N \otimes_R L$ for the contraction of the middle tensor factor, formed in Lean as the map $\mathrm{id}_N \otimes \varepsilon$ followed by the right unitor $N \otimes_R R \cong N$, tensored on the right with $\mathrm{id}_L$. Assume the cocycle identity in $((N \otimes_R L) \otimes_R L) \otimes_R L$: applying $\Delta$ to the outer (third) factor of $e$ and reassociating equals the result of applying $\Delta$ to the $L$-factor inside $N \otimes_R L$, reassociated, plus $e \otimes 1$, the associativity isomorphisms being those needed to place both sides in $((N \otimes_R L) \otimes_R L) \otimes_R L$. The conclusion is that $e$ is then the coboundary of $m$, namely $e = (\mathrm{id}_N \otimes \Delta)(m) - m \otimes 1$, where $(\mathrm{id}_N \otimes \Delta)(m) \in N \otimes_R (L \otimes_R L)$ is transported to $(N \otimes_R L) \otimes_R L$ by the inverse associativity isomorphism. Only the coalgebra structure of $L$ and the element $1 \in L$ enter.
--
--   This is the vanishing of the first cohomology of a cofree comodule: for the comodule $N \otimes_R L$ with coaction $\mathrm{id}_N \otimes \Delta$, the cobar complex has an explicit contracting homotopy given by contraction with the counit, so every $1$-cocycle is the coboundary of its counit contraction, with the cocycle written down explicitly rather than merely asserted to exist. It is used by [`HopfAlgebra.exists_eq_coaction_sub_tmul_one_of_cocycle`](thm.html#HopfAlgebra.exists_eq_coaction_sub_tmul_one_of_cocycle), and through it in the descent/invariant-generation step built on the fundamental theorem of Hopf modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Coalgebra.eq_lTensor_comul_sub_tmul_one_of_cocycle
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Bialgebra R L]
    {N : Type} [AddCommGroup N] [Module R N]
    (e : (N ⊗[R] L) ⊗[R] L)
    (he : (_root_.TensorProduct.assoc R (N ⊗[R] L) L L).symm ((Coalgebra.comul (R := R) (A := L)).lTensor (N ⊗[R] L) e) =
      ((_root_.TensorProduct.assoc R N L L).symm.toLinearMap.rTensor L)
          (((Coalgebra.comul (R := R) (A := L)).lTensor N).rTensor L e) +
        e ⊗ₜ[R] (1 : L)) :
    e = (_root_.TensorProduct.assoc R N L L).symm
          ((Coalgebra.comul (R := R) (A := L)).lTensor N
            ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e))) -
        ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e)) ⊗ₜ[R] (1 : L) := by sorry
