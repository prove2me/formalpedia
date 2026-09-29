-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul
-- name    : AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0359019e-5d7b-5d20-bd1c-84f127044530
-- title:
--   Points of μ_m^t are m-torsion; reduction is multiplicative
-- statement:
--   Let $S$ be a commutative ring, $T$ a commutative ring which is an $S$-algebra, and let $t,m$ be natural numbers. Write $\mathrm{muCoord}\,S\,t\,m$ for the additive monoid algebra $S[(\mathbb{Z}/m)^t]$ and $\mathrm{torusCoord}\,S\,t$ for $S[\mathbb{Z}^t]$, and let $F$ be the $S$-algebra map $S[\mathbb{Z}^t] \to S[(\mathbb{Z}/m)^t]$ obtained by functoriality of the monoid algebra from the additive homomorphism $\mathbb{Z}^t \to (\mathbb{Z}/m)^t$ given coordinatewise by evaluation at $i$ followed by the canonical map $\mathbb{Z} \to \mathbb{Z}/m$. On each of the monoids $\mathrm{WithConv}(S[(\mathbb{Z}/m)^t] \to_{\mathrm{alg}} T)$ and $\mathrm{WithConv}(S[\mathbb{Z}^t] \to_{\mathrm{alg}} T)$ of $S$-algebra homomorphisms with the convolution product, the theorem asserts three things simultaneously: first, every $\chi$ in $\mathrm{WithConv}(S[(\mathbb{Z}/m)^t] \to_{\mathrm{alg}} T)$ satisfies $\chi^m = 1$ for the convolution power and convolution unit; second, for all $\chi, \chi'$ the map sending an algebra homomorphism $\psi$ to $\psi \circ F$, read in the convolution monoid of $S[\mathbb{Z}^t]$-points, carries the convolution product of $\chi$ and $\chi'$ to the convolution product of the two images; third, that same map sends the convolution unit of $\mathrm{WithConv}(S[(\mathbb{Z}/m)^t] \to_{\mathrm{alg}} T)$ to the convolution unit of $\mathrm{WithConv}(S[\mathbb{Z}^t] \to_{\mathrm{alg}} T)$.
--
--   In geometric terms: the $T$-valued points of the diagonalisable group $\mu_{m,S}^t = D((\mathbb{Z}/m)^t)$ form an $m$-torsion group, and precomposition with the comorphism of the closed immersion $\mu_m^t \hookrightarrow \mathbb{G}_m^t$ (reduction of exponents modulo $m$) is a monoid homomorphism on points. It is used in the construction of lifts of points of the torus fibre over a Henselian base, in [`AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian`](thm.html#AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicGeometry AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul
    (S : Type u) [CommRing S] (T : Type u) [CommRing T] [Algebra S T] (t m : ℕ) :
    (∀ χ : WithConv (muCoord S t m →ₐ[S] T), χ ^ m = 1) ∧
    (∀ χ χ' : WithConv (muCoord S t m →ₐ[S] T),
      WithConv.toConv ((χ * χ').ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
        WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) * WithConv.toConv (χ'.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))) ∧
    (WithConv.toConv ((1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
      (1 : WithConv (torusCoord S t →ₐ[S] T))) := by sorry
