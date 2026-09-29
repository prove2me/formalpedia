-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree
-- name    : CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/5b0135d6-5f5b-55d4-aefe-3f32e0d0ded1
-- title:
--   Quotients with equal kernel ideals are isomorphic
-- statement:
--   Let $p$ be a prime and $B$ a Noetherian commutative ring. Let $\Phi, Y, Y'$ be formal $\mathcal{O}_D$-modules over $B$, i.e. two-dimensional commutative formal group laws over $B$ together with an additive and multiplicative action of $\mathbb{Z}_{p^2}$ by endomorphisms of the law and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma(a)]\circ\varpi$ for the Frobenius $\sigma$. Let $\rho, \rho'$ be pairs of power series in $B[\![x_1,x_2]\!]$ which are homomorphisms of formal $\mathcal{O}_D$-modules $\Phi \to Y$ and $\Phi \to Y'$ respectively: each has zero constant terms, is compatible with the two group laws, and commutes with the $\mathbb{Z}_{p^2}$-action and with $\varpi$. Assume that $\rho$ has kernel of degree $d$ for some natural number $d$, meaning that $B[\![x_1,x_2]\!]/(\rho_1,\rho_2)$ is a finite projective $B$-module whose base change along every ring homomorphism from $B$ to a field $\kappa$ has $\kappa$-dimension $d$; and assume the two kernel ideals coincide, $(\rho_1,\rho_2) = (\rho'_1,\rho'_2)$. Then there exist $u, v$, homomorphisms of formal $\mathcal{O}_D$-modules $Y \to Y'$ and $Y' \to Y$, with $v\circ u$ and $u\circ v$ both the identity and with $u\circ\rho = \rho'$ and $v\circ\rho' = \rho$. Uniqueness of $u$ and $v$ is not asserted.
--
--   This is the uniqueness of the quotient of a formal $\mathcal{O}_D$-module by a finite locally free kernel: two isogenies out of $\Phi$ with the same kernel ideal are identified by mutually inverse isomorphisms of their targets. It is used in the Čerednik–Drinfeld part of the development, both in the construction of the moduli scheme of special formal modules with prescribed kernel ideals and in the rigidification statement comparing translation maps with Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (Φ Y Y' : FormalODModule p B) (ρ ρ' : Series B)
    (hρ : FormalODModule.IsODHom Φ Y ρ) (hρ' : FormalODModule.IsODHom Φ Y' ρ')
    {d : ℕ} (hker : FormalODModule.HasKernelOfDegree ρ d)
    (hI : Ideal.span (Set.range ρ) = Ideal.span (Set.range ρ')) :
    ∃ u v : Series B, FormalODModule.IsODHom Y Y' u ∧ FormalODModule.IsODHom Y' Y v ∧
      v.comp u = Series.id B ∧ u.comp v = Series.id B ∧ u.comp ρ = ρ' ∧ v.comp ρ' = ρ := by sorry
