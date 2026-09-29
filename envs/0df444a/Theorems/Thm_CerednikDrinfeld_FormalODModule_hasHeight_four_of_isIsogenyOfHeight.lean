-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight
-- name    : CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/71c19533-e703-5f21-81ed-5958b3d87807
-- title:
--   Height 4 is preserved by isogenies of formal 𝒪_D-modules
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative Noetherian ring; assume $p$ is nilpotent in $B$. Let $X$ and $Y$ be formal $\mathcal{O}_D$-modules over $B$ in the sense of `FormalODModule p B`, that is, each carries a commutative two-dimensional formal group law together with an action `act` of `Zp2 p` and a further series `varpi`, all of whose components are endomorphisms of the law, satisfying `act 1 = id`, `act (a*b) = act a ∘ act b`, additivity of `act` in $a$ via the group law, `varpi ∘ varpi = act p` and `varpi ∘ act a = act (Frobenius a) ∘ varpi`. Let $\rho$ be a pair of power series in two variables over $B$ and $h$ a natural number, and assume `IsIsogenyOfHeight X Y ρ h`: $\rho$ is a homomorphism of laws from $X.F$ to $Y.F$ commuting with the `act` of every $a$ and with `varpi`, and it has kernel of degree $p^h$, i.e. the kernel algebra of $\rho$ is finite and projective as a $B$-module and, for every field $\kappa$ and every ring homomorphism $B \to \kappa$, the kernel algebra of the base-changed series has $\kappa$-dimension $p^h$. Assume further that $X$ has height $4$, meaning that the series `X.act p` has kernel of degree $p^4$ in this sense. The conclusion is that $Y$ has height $4$, i.e. `Y.act p` has kernel of degree $p^4$.
--
--   This records the invariance of the height of a formal $\mathcal{O}_D$-module under $\mathcal{O}_D$-linear isogenies, in the degree-of-kernel formulation used throughout the Čerednik–Drinfel'd part of the development. It is used in the study of the $\varpi$-divisible structure of special formal $\mathcal{O}_D$-modules and in the construction of the moduli scheme together with its closed immersion into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X Y : FormalODModule p B) (ρ : Series B) (h : ℕ)
    (hρ : FormalODModule.IsIsogenyOfHeight X Y ρ h) (hX : X.HasHeight 4) :
    Y.HasHeight 4 := by sorry
