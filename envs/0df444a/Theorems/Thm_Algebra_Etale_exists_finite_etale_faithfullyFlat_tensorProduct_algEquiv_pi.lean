-- Prove2me | Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
-- name    : Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/9d10fb49-1ee1-572e-902a-bb0a80467bb4
-- title:
--   Finite étale algebras over a Noetherian local ring split after finite étale base change
-- statement:
--   Let $R$ be a commutative ring in a fixed universe that is local and Noetherian, and let $B$ be a commutative ring in the same universe equipped with an $R$-algebra structure such that $B$ is finite as an $R$-module and étale as an $R$-algebra. The assertion is the existence of a type $R'$ in the same universe, together with a commutative ring structure on $R'$, an $R$-algebra structure making $R'$ finite as an $R$-module, étale as an $R$-algebra and faithfully flat as an $R$-module, and with $R'$ again a Noetherian ring, such that the $R'$-algebra $R' \otimes_R B$ is isomorphic, as an $R'$-algebra, to the product algebra $\mathrm{Fin}\,n \to R'$ where $n = \operatorname{finrank}_R B$ is the rank of $B$ as an $R$-module. The isomorphism is asserted in the form `Nonempty` of the type of $R'$-algebra equivalences, so only its existence, not a chosen one, is provided.
--
--   This is the local-base case of the statement that a finite étale cover becomes totally split after a finite étale faithfully flat base change, with the splitting degree recorded as the $R$-module rank of $B$. It is used in the construction of charts and sections for relative Picard schemes and in the relative group law for Jacobians of curves with good reduction, where one works over a Noetherian local (typically discrete valuation) base and then passes to a finite étale faithfully flat extension $R'$, which is again Noetherian but in general neither local nor connected.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

theorem Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by sorry
