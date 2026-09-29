-- Prove2me | Theorems.Thm_CohCarrier_transfer_transitive
-- name    : CohCarrier.transfer_transitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/81a72a15-6309-5def-b25c-c5c4b9c6d86d
-- title:
--   Transitivity of the transfer for K ≤ L ≤ G
-- statement:
--   Let $G$ be a group and $C$ a commutative group, and let $K \le L$ be subgroups of $G$, the inclusion being witnessed by `hKL : K ≤ L`. Assume $K$ and $L$ have finite index in $G$, and that the subgroup `K.subgroupOf L` — the preimage of $K$ in $L$, i.e. $K$ regarded as a subgroup of $L$ — has finite index in $L$. Let $\psi : K \to C$ be a group homomorphism. The transfer construction `MonoidHom.transfer` sends a homomorphism from a finite-index subgroup to $C$ to a homomorphism from the ambient group to $C$. The assertion is an equality of homomorphisms $G \to C$: the transfer of $\psi$ from $K$ to $G$ coincides with the iterated transfer obtained by first composing $\psi$ with the isomorphism `Subgroup.subgroupOfEquivOfLe hKL` from `K.subgroupOf L` onto $K$, transferring the resulting homomorphism `K.subgroupOf L → C` up to a homomorphism $L \to C$, and then transferring that from $L$ up to $G$. Equality is of the two homomorphisms themselves, hence holds at every $g \in G$.
--
--   This is the transitivity of the transfer (corestriction in degree one with trivial coefficients), $V_{G \to K} = V_{G \to L} \circ V_{L \to K}$ for a chain $K \le L \le G$ of finite-index subgroups. It is used in the computation of the corner term [`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_transfer_transitive.lean

import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.transfer_transitive {G : Type*} [Group G] {C : Type*} [CommGroup C] (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (ψ : K →* C) :
    MonoidHom.transfer ψ
      = MonoidHom.transfer
          (MonoidHom.transfer (ψ.comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)) := by sorry
