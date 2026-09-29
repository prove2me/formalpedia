-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
-- name    : AlgebraicCurve.Divisor.correspondence_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/010db077-0875-5e9f-8c17-aaf058f72671
-- title:
--   Correspondence of a multiple of a single place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and assume $F'$ has principal divisors over $K$, i.e. every nonzero $f \in F'$ admits a finitely supported integer-valued function on the places of $F'$ whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$. Let $\varphi, \psi : F \to F'$ be two $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, so that each makes $F'$ an integral $F$-algebra; let $v$ be a place of $F$ over $K$ (a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring), and let $n \in \mathbb{Z}$. The assertion is that the correspondence attached to the pair $(\varphi,\psi)$, namely the pullback of divisors along $\varphi$ followed by the pushforward along $\psi$, sends the divisor $n\,v$ (the finitely supported function `Finsupp.single v n`) to $$\sum_{w \in \mathrm{fiberAlong}\,\varphi\,v} \bigl(n \cdot e_{\varphi}(w) \cdot f_{\psi}(w)\bigr)\,\bigl(w|_{\psi}\bigr),$$ the sum over the finite set of places $w$ of $F'$ in the fibre of $v$ for the $F$-algebra structure given by $\varphi$, where $e_{\varphi}(w)$ is the ramification index of $w$ for that structure, $f_{\psi}(w)$ the inertia degree of $w$ for the $F$-algebra structure given by $\psi$, and $w|_{\psi}$ the restriction of $w$ to $F$ along $\psi$.
--
--   This is the explicit formula for a correspondence $\psi_* \circ \varphi^*$ on divisors evaluated on a multiple of a single place, the divisor-theoretic bookkeeping underlying correspondences between function fields. It is used for support computations for such correspondences and, in the modular-curve layer, for the identification of Hecke correspondences on places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_single.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.Divisor.correspondence_single {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = ∑ w ∈ Place.fiberAlong φ hφ v, Finsupp.single (w.restrictAlong ψ hψ) (n * (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by sorry
