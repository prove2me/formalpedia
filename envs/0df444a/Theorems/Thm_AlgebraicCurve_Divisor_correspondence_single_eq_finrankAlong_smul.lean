-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_eq_finrankAlong_smul
-- name    : AlgebraicCurve.Divisor.correspondence_single_eq_finrankAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cc61a680-9513-534d-af46-472e995da31a
-- title:
--   Correspondence acts on a prime divisor by the degree
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and assume $F'$ has principal divisors over $K$: every nonzero $f \in F'$ is the divisor of a finitely supported $\mathbb{Z}$-valued function on the places of $F'$ over $K$ whose value at each place is $\operatorname{ord}$ of $f$ and whose degree is $0$ (places being valuation subrings of $F'$, proper, containing the image of $K$, and principal ideal rings). Let $\varphi, \psi : F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, and suppose that $F'$ is a finite module over $F$ via $\varphi$ and separable over $F$ via $\varphi$. Let $v$ be a place of $F$ over $K$ and assume that every place $w$ in the fibre of $\varphi$ above $v$ restricts along $\psi$ to $v$ again, and that $w$ has inertia (residue) degree $1$ both along $\psi$ and along $\varphi$. Then for every $n \in \mathbb{Z}$ the correspondence $\psi_* \circ \varphi^*$ sends the divisor $n\,v$ to $[F':F]_\varphi \cdot n\,v$, where $[F':F]_\varphi$ is the $F$-rank of $F'$ taken along $\varphi$.
--
--   This is the generic eigenvector statement underlying the Eisenstein eigenvalue of a Hecke correspondence on a cuspidal divisor: a prime divisor whose whole $\varphi$-fibre collapses back onto it along $\psi$, with residue degrees one on both legs, is an eigenvector of $\psi_* \circ \varphi^*$ with eigenvalue the degree of the pull-back leg. It is used in the analysis of degeneracy maps between modular curves of level $N$ and $N\ell$ and of the correspondence they define on divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_single_eq_finrankAlong_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.Divisor.correspondence_single_eq_finrankAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (hfψ : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong ψ hψ = 1) (hfφ : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong φ hφ = 1) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = (finrankAlong K φ : ℤ) • Finsupp.single v n := by sorry
