-- Prove2me | Theorems.Thm_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
-- name    : Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7cbf2a80-d43c-5d96-bdba-ef9ae22e1273
-- title:
--   Surjection of formally smooth local k-algebras with no cotangent rank drop is injective
-- statement:
--   Let $k$ be a field and let $P$, $S$ be commutative local rings in the same universe, with $P$ Noetherian, equipped with $k$-algebra structures and a $P$-algebra structure on $S$ compatible with the $k$-algebra structures (a scalar tower $k \to P \to S$). Assume $P$ and $S$ are formally smooth over $k$, that the module of Kähler differentials $\Omega_{P/k}$ is a finite $P$-module, and that the structure map $P \to S$ is surjective. Write $\kappa$ for the residue field of the local ring $S$. Assume the inequality of $\kappa$-dimensions
--   $$\dim_\kappa\bigl(\kappa \otimes_S (S \otimes_P \Omega_{P/k})\bigr) \le \dim_\kappa\bigl(\kappa \otimes_S \Omega_{S/k}\bigr).$$
--   Then the kernel of the ring homomorphism $P \to S$ is the zero ideal; that is, the surjection $P \to S$ is an isomorphism. Only the inequality $\le$ is assumed, the reverse one being automatic from the conormal sequence.
--
--   This is the local algebraic form of the statement that a closed immersion of smooth schemes over a field which does not drop the rank of the sheaf of differentials at a point is an isomorphism near that point (EGA IV 17.12.1). It is used in the proof of [`Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le`](thm.html#Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le), the step producing vanishing of an ideal from a smoothness-plus-dimension comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
    {k P S : Type u} [Field k] [CommRing P] [CommRing S] [IsLocalRing P] [IsLocalRing S] [IsNoetherianRing P]
    [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [Algebra.FormallySmooth k P] [Algebra.FormallySmooth k S] [Module.Finite P Ω[P⁄k]]
    (hPS : Function.Surjective (algebraMap P S))
    (hrank : Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P] Ω[P⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k])) :
    RingHom.ker (algebraMap P S) = ⊥ := by sorry
