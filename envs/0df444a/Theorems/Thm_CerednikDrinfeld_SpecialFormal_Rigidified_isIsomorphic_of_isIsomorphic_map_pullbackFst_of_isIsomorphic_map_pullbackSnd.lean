-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b6dbf0e1-f586-5617-92fa-9ec25b2e1646
-- title:
--   Uniqueness of gluing for admissible rigidified objects
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota\colon W(\mathbb{F}_{p^2})\to O$, and let $\Phi$ be a formal $\mathcal{O}_D$-module of dimension $2$ over $O/pO$ (a two-variable commutative formal group together with an action of $W(\mathbb{F}_{p^2})$ and a series $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$), assumed special for the structure map $O\to O/pO$ composed with $\iota$ — that is, the Lie algebra is the direct sum of the two invertible eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ — and of height $4$, meaning that the kernel algebra of $[p]$ is finite projective of rank $p^4$ at every field-valued point. Let $B,B',B''$ be Noetherian commutative rings with structure maps $\psi,\psi',\psi''$ from $O$ and with $p$ nilpotent in each, and let $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ be surjective ring homomorphisms compatible with the structure maps and with nilpotent kernels. Write $P$ for the fibre product `pullbackRing` $\varphi'\,\varphi''$, the subring of $B'\times B''$ on which $\varphi'\circ\mathrm{fst}=\varphi''\circ\mathrm{snd}$, assume $p$ nilpotent in $P$, and let $\psi_P\colon O\to P$ be a structure map whose composites with the two projections `pullbackFst` and `pullbackSnd` are $\psi'$ and $\psi''$. Let $t_1,t_2$ be rigidified objects over $P$, each consisting of a formal $\mathcal{O}_D$-module $X$ over $P$, a natural number $n$ and a series $\rho$ over $P/pP$, and assume both are admissible for $(\iota,\psi_P)$: $X$ is special for $\psi_P\circ\iota$, $X$ has height $4$, and $\rho$ is an $\mathcal{O}_D$-isogeny of height $4n$ from the base change of $\Phi$ to $\bar X=X\otimes P/pP$. If the base changes of $t_1$ and $t_2$ along `pullbackFst` and along `pullbackSnd` (apply the projection to $X$ and the induced map $P/pP\to B'/pB'$, resp. $P/pP\to B''/pB''$, to $\rho$, keeping $n$) are isomorphic in each case, then $t_1$ and $t_2$ are isomorphic: there are series $u,v$ over $P$ and an $m\in\mathbb{N}$ with $u$ an $\mathcal{O}_D$-homomorphism $t_1.X\to t_2.X$, $v$ one in the opposite direction, $v\circ u$ and $u\circ v$ both the identity, and $[p^{m+t_2.n}]\circ(\bar u\circ t_1.\rho)=[p^{m+t_1.n}]\circ t_2.\rho$ on $t_2.\bar X$.
--
--   This is the uniqueness half of the gluing statement for the Čerednik–Drinfeld moduli problem of special formal $\mathcal{O}_D$-modules of height $4$ with rigidification, as in Boutot–Carayol II (10.2): admissible rigidified objects over a fibre product of two surjections with nilpotent kernels are determined up to isomorphism by their two base changes. It feeds the verification that the associated moduli package satisfies the Zariski-sheaf descent condition for such squares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p O)).comp ι)) (hΦ4 : Φ.HasHeight 4)
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (ψP : O →+* ModuliPackage.pullbackRing φ' φ'')
    (hψP' : (ModuliPackage.pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (ModuliPackage.pullbackSnd φ' φ'').comp ψP = ψ'')
    (t₁ t₂ : Rigidified p Φ (ModuliPackage.pullbackRing φ' φ''))
    (h₁ : t₁.IsAdmissible ι ψP) (h₂ : t₂.IsAdmissible ι ψP)
    (h' : (t₁.map (ModuliPackage.pullbackFst φ' φ'')).IsIsomorphic (t₂.map (ModuliPackage.pullbackFst φ' φ'')))
    (h'' : (t₁.map (ModuliPackage.pullbackSnd φ' φ'')).IsIsomorphic (t₂.map (ModuliPackage.pullbackSnd φ' φ''))) :
    t₁.IsIsomorphic t₂ := by sorry
