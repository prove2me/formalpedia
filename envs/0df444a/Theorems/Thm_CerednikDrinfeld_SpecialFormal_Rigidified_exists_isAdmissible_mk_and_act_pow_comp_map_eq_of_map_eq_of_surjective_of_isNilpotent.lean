-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6e9b9e7a-dc1b-513c-ac47-098cb9f99d4e
-- title:
--   Lifting a rigidification along a nilpotent thickening
-- statement:
--   Fix a prime $p$ and a commutative ring $O$ with a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to O$ (here `Zp2 p` is the Witt vectors of the field with $p^2$ elements), and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$, i.e. an object of `FormalODModule p (O ⧸ pIdeal p O)`. Let $R,S$ be Noetherian commutative rings, $\pi\colon R\to S$ a surjective ring homomorphism whose kernel is a nilpotent ideal, with $p$ nilpotent in $R$, and let $\psi_R\colon O\to R$, $\psi_S\colon O\to S$ satisfy $\psi_S=\pi\circ\psi_R$. Let $X$ be a formal $\mathcal{O}_D$-module over $R$ which is special for the structure map $\psi_R\circ\iota$ (the submodules `lieZero` and `lieOne` attached to that map are complementary and each invertible over $R$) and of height $4$, meaning the series $X.\mathrm{act}(p)$ has kernel of degree $p^4$. Let $t'=(t'.X,t'.n,t'.\rho)$ be a rigidified triple over $S$ consisting of a formal $\mathcal{O}_D$-module over $S$, a natural number and a $2$-tuple of power series over $S/pS$, assumed admissible for $\iota,\psi_S$: $t'.X$ is special for $\psi_S\circ\iota$, has height $4$, and `FormalODModule.IsIsogenyOfHeight` holds for the reduction `Φbar` of $\Phi$ determined by $\psi_S$, for $t'.X$ reduced modulo $p$, for $t'.\rho$ and for the height parameter $4\,t'.n$. Assume moreover $X\otimes_R S = t'.X$, i.e. `X.map π = t'.X`. Then there exist $n\in\mathbb{N}$ and a $2$-tuple of power series $\rho$ over $R/pR$ such that the triple $\langle X,n,\rho\rangle$ is admissible for $\iota,\psi_R$ — so $\rho$ satisfies `IsIsogenyOfHeight` from the reduction of $\Phi$ determined by $\psi_R$ to $X$ modulo $p$ with height parameter $4n$ — and there exists $m\in\mathbb{N}$ with $$[p^{m+t'.n}]\circ(\rho\bmod p)=[p^{m+n}]\circ t'.\rho$$ as series over $S/pS$, where $[p^k]$ denotes $t'.X$ reduced modulo $p$ acted on by $p^k\in\mathbb{Z}_{p^2}$ and $\rho\bmod p$ is the image of $\rho$ under the induced map $R/pR\to S/pS$.
--
--   This is the lifting (smoothness) step for admissible rigidified triples in the Čerednik–Drinfeld setting: along a nilpotent thickening $R\to S$ with $p$ nilpotent, a rigidification of the reduction of a special height-$4$ formal $\mathcal{O}_D$-module extends to a rigidification over $R$, the two rigidifications agreeing after composing with a common power of $p$ (which is the relevant equivalence of quasi-isogenies). It is used in the constructions of admissible triples over $R$ compatible with prescribed data over $S$, in particular in the comparison of base changes along the two projections of a pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hR : IsNilpotent (p : R))
    (ψR : O →+* R) (ψS : O →+* S) (hψ : π.comp ψR = ψS)
    (X : FormalODModule p R) (hXs : X.IsSpecial (structureMap ι ψR)) (hX4 : X.HasHeight 4)
    (t' : Rigidified p Φ S) (ht' : t'.IsAdmissible ι ψS) (hX : X.map π = t'.X) :
    ∃ (n : ℕ) (ρ : Series (R ⧸ pIdeal p R)),
      (⟨X, n, ρ⟩ : Rigidified p Φ R).IsAdmissible ι ψR ∧
      ∃ m : ℕ, (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp (ρ.map (reduceMap π)) =
        (t'.Xbar.act ((p : Zp2 p) ^ (m + n))).comp t'.ρ := by sorry
