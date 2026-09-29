-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/e9c94fe4-c129-5704-88b1-829a7a2cf653
-- title:
--   Gluing admissible rigidified triples along a ring fibre product
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$ (a two-dimensional commutative formal group law with a $\mathbb{Z}_{p^2}$-action and a uniformiser series $\varpi$) which is special for the composite $\mathbb{Z}_{p^2} \to O \to O/pO$, meaning its Lie algebra is the direct sum of the two invertible eigenmodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$, and which has height $4$, i.e. the series giving multiplication by $p$ has kernel algebra of degree $p^4$. Let $B$, $B'$, $B''$ be Noetherian commutative rings with structure maps $\psi \colon O \to B$, $\psi' \colon O \to B'$, $\psi'' \colon O \to B''$ in which $p$ is nilpotent, and let $\varphi' \colon B' \to B$, $\varphi'' \colon B'' \to B$ be surjective homomorphisms over $O$ (that is, $\varphi' \circ \psi' = \psi$ and $\varphi'' \circ \psi'' = \psi$) with nilpotent kernels. Let $P = \mathrm{pullbackRing}\,\varphi'\,\varphi''$ be the subring of $B' \times B''$ on which $\varphi'$ and $\varphi''$ agree, assume $p$ nilpotent in $P$, and let $\psi_P \colon O \to P$ be a structure map whose composites with the two projections $\mathrm{pullbackFst}$ and $\mathrm{pullbackSnd}$ are $\psi'$ and $\psi''$. Given rigidified triples $t' = (X',n',\rho')$ over $B'$ and $t'' = (X'',n'',\rho'')$ over $B''$ which are admissible for $(\iota,\psi')$ and $(\iota,\psi'')$ — each underlying formal $\mathcal{O}_D$-module special for the relevant structure map $\mathbb{Z}_{p^2} \to B'$ resp. $\mathbb{Z}_{p^2} \to B''$ and of height $4$, with $\rho$ an isogeny of height $4n$ from the base change of $\Phi$ to the reduction of $X$ mod $p$ — and assuming that the base changes $t'\otimes_{B'}B$ and $t''\otimes_{B''}B$ along $\varphi'$ and $\varphi''$ are isomorphic in the sense of `IsIsomorphic` (mutually inverse $\mathcal{O}_D$-homomorphisms compatible with the rigidifications after multiplication by a suitable power of $p$), the conclusion is that there exists a rigidified triple $t$ over $P$, admissible for $(\iota,\psi_P)$, whose base changes along $\mathrm{pullbackFst}$ and $\mathrm{pullbackSnd}$ are isomorphic to $t'$ and to $t''$ respectively.
--
--   This is the existence half of the gluing property of Drinfeld's moduli functor of special formal $\mathcal{O}_D$-modules along a fibre product of rings with surjective nilpotent-kernel legs, in the form used by Boutot and Carayol, read on rigidified triples rather than on sheafified functors. It feeds the verification that the associated moduli package has the pullback property needed for the Zariski-sheaf statement [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
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
    (t' : Rigidified p Φ B') (t'' : Rigidified p Φ B'')
    (ht' : t'.IsAdmissible ι ψ') (ht'' : t''.IsAdmissible ι ψ'')
    (h : (t'.map φ').IsIsomorphic (t''.map φ'')) :
    ∃ t : Rigidified p Φ (ModuliPackage.pullbackRing φ' φ''),
      t.IsAdmissible ι ψP ∧
      (t.map (ModuliPackage.pullbackFst φ' φ'')).IsIsomorphic t' ∧
      (t.map (ModuliPackage.pullbackSnd φ' φ'')).IsIsomorphic t'' := by sorry
