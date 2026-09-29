-- Prove2me | Theorems.Thm_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed
-- name    : AlgHom.natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/7977c893-69e2-5483-b5c3-c010799c7a66
-- title:
--   Transitive automorphism action makes #Hom_k(B,k) divide dim_k B
-- statement:
--   Let $k$ be a field in universe $u$ which is algebraically closed, and let $B$ be a commutative ring in universe $v$ equipped with a $k$-algebra structure such that $B$ is a finite $k$-module, i.e. finitely generated as a $k$-module (hence finite-dimensional as a $k$-vector space). Assume the transitivity hypothesis `htrans`: for every pair of $k$-algebra homomorphisms $\varphi, \psi : B \to k$ there exists a $k$-algebra automorphism $\sigma$ of $B$ with $\varphi \circ \sigma = \psi$, where $\sigma$ is viewed as a $k$-algebra endomorphism of $B$ and the composite is taken as $k$-algebra maps. The conclusion is a divisibility of natural numbers: the cardinality of the type $B \to_{\mathrm{alg}[k]} k$ of $k$-algebra homomorphisms $B \to k$, taken as `Nat.card` (so $0$ if that type is infinite, which here it is not), divides the $k$-dimension `Module.finrank k B` of $B$.
--
--   This is the standard counting statement behind the divisibility of the rank of a finite algebra by the number of its geometric points when the automorphism group acts transitively on those points; the degenerate case $B = 0$ is covered, both sides then being $0$. It is used in the construction of the relative group law on Jacobians of curves with good reduction, via [`GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer`](thm.html#GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AlgHom.natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed
    (k : Type u) (B : Type v) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Module.Finite k B]
    (htrans : ∀ φ ψ : B →ₐ[k] k, ∃ σ : B ≃ₐ[k] B, φ.comp (σ : B →ₐ[k] B) = ψ) :
    Nat.card (B →ₐ[k] k) ∣ Module.finrank k B := by sorry
