-- Prove2me | Theorems.Thm_DetDLP_tapered_hermite_recovery_weights
-- name    : DetDLP.tapered_hermite_recovery_weights
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T15:34:01.4657+00:00
-- url     : https://prove2.me/theorems/cf92e2ca-3a45-46c1-8950-bfdbf596b3d4
-- title:
--   Bounded rational Hermite weights for all coefficient algebras
-- statement:
--   On the nonzero dyadic residue classes modulo 2^(a+1), the jets at any integer representatives recover evaluation at zero for every polynomial of degree at most M(2^(a+1)-1) over every commutative rational algebra. The same individual rational weights work throughout. For a node of valuation v, each nonzero weight has valuation at least -(6h·2^(a-v)+4M(a+1)) when 3M ≤ hu ≤ 4M. This bounds the denominators of the weights on each individual branch of a terminal expansion.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.1, actual interpolation weights and the denominator loss used in Section 5.3.

import Mathlib

set_option autoImplicit false

namespace DetDLP

open Finset Polynomial

theorem tapered_hermite_recovery_weights (a M h u : ℕ) (hm : 0<M) (lo : 3*M≤h*u) (high : h*u≤4*M)
    (r : ZMod (2^(a+1))→ℤ) (hr : ∀ t,((r t:ℤ):ZMod (2^(a+1)))=t) :
    let T := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥T) := padicValNat 2 t.val.val
    let m (t : ↥T) := h*(u-v t)
    ∃ w : ↥T→ℕ→ℚ, (∀ t j,w t j=0 ∨ -(6*(h:ℤ)*2^(a-v t)+4*M*(a+1))≤padicValRat 2 (w t j)) ∧
      ∀ (A : Type) [CommRing A] [Algebra ℚ A] (F : A[X]),F.natDegree≤M*(2^(a+1)-1) →
        F.eval 0=∑ t : ↥T,∑ j∈range (m t),algebraMap ℚ A (w t j)*
          (F.comp (C (algebraMap ℚ A (r t.val:ℚ))+C (algebraMap ℚ A ((2:ℚ)^(a+1)))*X)).coeff j := by sorry

end DetDLP
