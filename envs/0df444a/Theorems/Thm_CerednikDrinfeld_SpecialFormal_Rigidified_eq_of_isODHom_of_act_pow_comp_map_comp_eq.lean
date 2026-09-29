-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/18296096-47dc-53e3-ac6c-a964f6ea8865
-- title:
--   Rigidity of homomorphisms compatible with rigidifications
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, and $\Phi$ a formal $\mathcal O_D$-module over $O/pO$ — that is, a two-dimensional commutative formal group law together with an action of $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$ by law endomorphisms and a law endomorphism $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma(a)]\circ\varpi$. Let $B$ be a Noetherian commutative ring in which $p$ is nilpotent, and let $\iota\colon \mathbb Z_{p^2}\to O$ and $\psi\colon O\to B$ be ring homomorphisms. Let $t = (X,n,\rho)$ and $t' = (X',n',\rho')$ be rigidified objects over $B$, each consisting of a formal $\mathcal O_D$-module over $B$, a natural number, and a pair $\rho$ of power series in two variables over $B/pB$. Assume $t$ is admissible for $(\iota,\psi)$: $X$ is special for the structure map built from $\iota$ and $\psi$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ along $\psi$ to $\bar X = X\otimes B/pB$. Assume the constant terms of $\rho'$ vanish. Let $u_1,u_2$ be pairs of power series over $B$ that are both $\mathcal O_D$-linear homomorphisms $X\to X'$, i.e. law homomorphisms commuting with the $\mathbb Z_{p^2}$-action and with $\varpi$, and suppose that for some $m_1,m_2\in\mathbb N$ one has $[p^{m_i+n'}]_{\bar X'}\circ \bar u_i\circ\rho = [p^{m_i+n}]_{\bar X'}\circ\rho'$ over $B/pB$, where $\bar u_i$ is the reduction of $u_i$. Then $u_1 = u_2$.
--
--   This is the rigidity statement underlying the Drinfeld moduli problem: a homomorphism between admissible rigidified formal $\mathcal O_D$-modules is determined by its compatibility with the rigidifications, so that isomorphisms witnessing `IsIsomorphic` are unique and admissible objects have no nontrivial automorphisms. It is used in the descent and gluing arguments for the isomorphism relation on rigidified objects, namely the comparison with isomorphisms over Artinian rings and the statements that isomorphy may be checked after localisation away from an element or on the two factors of a pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (ι : Zp2 p →+* O) (ψ : O →+* B) (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (u₁ u₂ : Series B) (m₁ m₂ : ℕ)
    (hu₁ : FormalODModule.IsODHom t.X t'.X u₁) (hu₂ : FormalODModule.IsODHom t.X t'.X u₂)
    (h₁ : (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t'.n))).comp
        ((u₁.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t.n))).comp t'.ρ)
    (h₂ : (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t'.n))).comp
        ((u₂.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t.n))).comp t'.ρ) :
    u₁ = u₂ := by sorry
