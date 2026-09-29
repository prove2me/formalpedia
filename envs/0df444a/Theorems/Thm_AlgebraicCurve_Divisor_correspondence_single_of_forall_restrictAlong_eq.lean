-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq
-- name    : AlgebraicCurve.Divisor.correspondence_single_of_forall_restrictAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/22d9e811-3d3e-5535-b852-7010195f6e8a
-- title:
--   Collapse of a correspondence on a single place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and assume $F'$ has principal divisors over $K$, i.e. every nonzero $f \in F'$ admits a divisor of degree $0$ whose coefficient at each place is $\mathrm{ord}_v(f)$. Let $\varphi, \psi : F \to F'$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, and let $v$ be a place of $F$ over $K$ (a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring). Assume that every place $w$ of $F'$ in the fibre of $v$ along $\varphi$ — the places of $F'$ lying over $v$ when $F'$ is viewed as an $F$-algebra through $\varphi$, a finite set — restricts along $\psi$ back to $v$. Then for every $n \in \mathbb{Z}$, the correspondence attached to $(\varphi, \psi)$, namely pullback of divisors along $\varphi$ followed by pushforward along $\psi$, sends the divisor $n\,v$ (the finitely supported function $\mathrm{single}\ v\ n$ on places of $F$) to the divisor supported at $v$ with coefficient $n \cdot \sum_{w} e_\varphi(w) f_\psi(w)$, the sum being over the fibre of $v$ along $\varphi$, where $e_\varphi(w)$ is the ramification index of $w$ along $\varphi$ and $f_\psi(w)$ the inertia degree of $w$ along $\psi$.
--
--   This is the degenerate case of the evaluation of a push–pull correspondence on a prime divisor: when the whole fibre restricts back to the starting place, the image is again a multiple of that place, with multiplicity the sum of the local products $e_\varphi f_\psi$. It is used for the computation of Hecke correspondences on cuspidal divisors of modular curves and in the comparison of such a correspondence with a multiplication by a degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.Divisor.correspondence_single_of_forall_restrictAlong_eq {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = Finsupp.single v (n * ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by sorry
