-- Prove2me | Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
-- name    : AdicCompletion.isNoetherianRing_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/f17a1005-966d-5e5b-803e-248d10af5016
-- title:
--   Adic completion of a Noetherian ring is Noetherian
-- statement:
--   Let $R$ be a commutative ring which is Noetherian as a ring, and let $I$ be an ideal of $R$. Then the $I$-adic completion `AdicCompletion I R`, that is the inverse limit $\varprojlim_k R/I^k$ of the quotients of $R$ by the powers of $I$ along the canonical projections, carried with its ring structure, is again a Noetherian ring. No finiteness or separatedness hypothesis on $I$ or on the filtration is imposed beyond the Noetherian hypothesis on $R$, and $I$ is an arbitrary ideal: in particular $I$ need not be proper, and the statement is one about the ring structure of the completion, asserting that every ideal of $\varprojlim_k R/I^k$ is finitely generated.
--
--   This is the classical statement that completion preserves the Noetherian property (Atiyah–Macdonald, Theorem 10.26). It underlies the commutative algebra of complete local and semilocal rings used throughout the deformation-theoretic part of the argument, and is invoked by the results on base change, flatness and power series presentations of adic completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem AdicCompletion.isNoetherianRing_of_isNoetherianRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by sorry
