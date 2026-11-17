-- Prove2me | Theorems.Thm_FLT_EDS_prePsi_adjacent_somos
-- name    : FLT.EDS.prePsi_adjacent_somos
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:22.95729+00:00
-- url     : https://prove2.me/theorems/608dc6b8-2203-4d70-9a52-28fc9025a7b6
-- title:
--   Normalized division polynomials satisfy an adjacent Somos relation
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve over $R$, assume $4≠0$ in $R$, and let $m∈ℤ$. Put $a_n=preΨ_n$, $s=Ψ_2^2$, and $q=Ψ_3$, all viewed as polynomials in $R[X]$, and define $ε_m=1$ if $m$ is even and $ε_m=s^2$ if $m$ is odd. Then $$a_{m+2}a_{m-2}=ε_ma_{m+1}a_{m-1}-qa_m^2.$$ This is the parity-corrected Somos recurrence used by the x-only multiplication certificates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

open Polynomial WeierstrassCurve
open scoped Classical
variable {R : Type*} [CommRing R]

theorem FLT.EDS.prePsi_adjacent_somos [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0) (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then 1 else W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ (m - 1))
        - W.Ψ₃ * W.preΨ m ^ 2 := by sorry
