-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight
-- name    : CerednikDrinfeld.FormalODModule.eq_of_natCast_pow_mul_eq_of_hasHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9c3a7348-2a51-553f-9d81-9247a5829dac
-- title:
--   Cancellation by pᵈ in End(X) for finite height
-- statement:
--   Fix a prime $p$ and a commutative Noetherian ring $B$, and let $X$ be a formal $\mathcal{O}_D$-module over $B$ in the sense of the project's structure `FormalODModule`: a $2$-dimensional commutative formal group law $X.F$ over $B$, together with an action `X.act` of $\mathbb{Z}_{p^2}$ and a uniformiser series `X.varpi`, all given by pairs of power series in two variables with zero constant term that are endomorphisms of the group law, subject to the usual multiplicativity, additivity and Frobenius-semilinearity relations. Assume `X.HasHeight h` for some natural number $h$, i.e. that the series $X.\mathrm{act}(p)$ has kernel of degree $p^h$: the associated kernel algebra is finite and projective as a $B$-module, and for every field $\kappa$ and every ring homomorphism $B \to \kappa$ the base-changed kernel algebra has $\kappa$-dimension $p^h$. Let $d$ be a natural number and let $x, y$ be endomorphisms of the formal group law $X.F$, the ring [`MvFormalGroup.End X.F`](def/MvFormalGroup_BasicV2.html#L242) having composition as multiplication. If the images of $x$ and $y$ under multiplication by the natural-number cast $p^d$ agree, i.e. $p^d \cdot x = p^d \cdot y$ in [`MvFormalGroup.End X.F`](def/MvFormalGroup_BasicV2.html#L242), then $x = y$. Thus $p^d$ is a left non-zero-divisor in the endomorphism ring; only the finite locally free kernel of $X.\mathrm{act}(p)$ enters, the exact value $p^h$ of its degree being irrelevant.
--
--   This is the standard cancellation property of the central integers $p^d$ in the endomorphism ring of a formal module of finite height, the formal-module analogue of the fact that isogenies of $p$-divisible groups can be divided by $p$ at most in a unique way. It supplies the cancellation input used in the construction and comparison of dual germs and of Atkin–Lehner type quotients for fake elliptic curves in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.eq_of_natCast_pow_mul_eq_of_hasHeight
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) {h : ℕ} (hX : X.HasHeight h) (d : ℕ) (x y : MvFormalGroup.End X.F)
    (hxy : ((p ^ d : ℕ) : MvFormalGroup.End X.F) * x = ((p ^ d : ℕ) : MvFormalGroup.End X.F) * y) : x = y := by sorry
