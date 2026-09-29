-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/5822f6b3-824e-525d-add2-c1d0d18e97b3
-- title:
--   Bijectivity from characteristic p, local lifting and Zariski descent
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, and let $G,H$ be moduli packages over $O$ at $p$, i.e. data assigning to every commutative ring $B$ with a ring map $\psi : O \to B$ such that $p$ is nilpotent in $B$ a set `obj`, together with functorial transition maps along ring maps compatible with the $O$-structures. Assume $G$ and $H$ satisfy `IsZariskiSheaf`: for every basic open cover of $\operatorname{Spec} B$ given by $f_1,\dots,f_n$ generating the unit ideal, sections are determined by their images in arbitrary models of the localisations $B[1/f_i]$, and families of sections over the $B[1/f_i]$ agreeing in the $B[1/f_if_j]$ glue. Let $\xi_B : G(B) \to H(B)$ be given for Noetherian $B$ with $p$ nilpotent, commuting with all transition maps along ring maps between Noetherian such $B$ (hypothesis $h\xi$). Assume that for $G$ and separately for $H$, given Noetherian $B,B',B''$ with $O$-structures and $p$ nilpotent, surjections $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ compatible with the $O$-structures and with nilpotent kernels, such that $p$ is nilpotent in the fibre product ring $B' \times_B B''$ (realised as the equaliser subring of $B' \times B''$, with its induced $O$-structure), any pair of sections over $B'$ and $B''$ with the same image over $B$ has a unique common lift to the fibre product. Assume the local lifting hypothesis: for Noetherian $B,B'$ as above and a surjection $\varphi : B' \to B$ compatible with the $O$-structures whose kernel has square $(0)$, and $x \in G(B)$ such that $\xi_B(x)$ lifts to $H(B')$, there are $f_1,\dots,f_n \in B'$ generating the unit ideal such that for each $i$, every Noetherian model $L'$ of $B'[1/f_i]$ and $L$ of $B[1/\varphi(f_i)]$ in which $p$ is nilpotent, and every ring map $L' \to L$ compatible with the localisation maps and $\varphi$ and with the $O$-structures, the image of $x$ in $G(L)$ admits a preimage in $G(L')$. Finally assume $\xi_B$ is bijective whenever $B$ is Noetherian with $p \cdot 1_B = 0$. Then $\xi_B$ is bijective for every Noetherian $B$ with an $O$-structure $\psi$ and $p$ nilpotent in $B$.
--
--   This is the formal counterpart of the Boutot–Carayol criterion (Astérisque 196–197, II (10.5)) for a morphism of moduli functors on nilpotent $O$-algebras to be an isomorphism, here in a Noetherian, Zariski-sheaf formulation in which liftability along square-zero extensions is only required locally on the base. It is used to show that the period map of the Čerednik–Drinfeld uniformisation is bijective, via [`CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isNoetherianRing_of_lieVarpi_eq_zero`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isNoetherianRing_of_lieVarpi_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_forall_charP_bijective_of_locallyLiftsAlong_noetherian_of_isZariskiSheaf
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (G H : CerednikDrinfeld.SpecialFormal.ModuliPackage.{0, 0} p O)
    (hGsh : G.IsZariskiSheaf) (hHsh : H.IsZariskiSheaf)
    (ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      G.obj B ψ hB → H.obj B ψ hB)
    (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (f : B →+* B') (hf : f.comp ψ = ψ') (x : G.obj B ψ hB),
      ξ B' ψ' hB' (G.map hB hB' f hf x) = H.map hB hB' f hf (ξ B ψ hB x))
    (hG : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : G.obj B' ψ' hB') (x'' : G.obj B'' ψ'' hB''),
      G.map hB' hB φ' hφ' x' = G.map hB'' hB φ'' hφ'' x'' →
      ∃! z : G.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        G.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        G.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hH : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : H.obj B' ψ' hB') (x'' : H.obj B'' ψ'' hB''),
      H.map hB' hB φ' hφ' x' = H.map hB'' hB φ'' hφ'' x'' →
      ∃! z : H.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        H.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        H.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')

    (hlift : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_hφs : Function.Surjective φ)
      (_hφ2 : RingHom.ker φ * RingHom.ker φ = ⊥) (x : G.obj B ψ hB),
      (H.fibre hB' hB φ hφ (ξ B ψ hB x)).Nonempty →
      ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : Fin n) (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
          (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
          (hL' : IsNilpotent (p : L')) (hL : IsNilpotent (p : L))
          (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp φ)
          (hφLψ : φL.comp ((algebraMap B' L').comp ψ') = (algebraMap B L).comp ψ),
          (G.fibre hL' hL φL hφLψ (G.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl x)).Nonempty)

    (hbase : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      (p : B) = 0 → Function.Bijective (ξ B ψ hB))

    (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) :
    Function.Bijective (ξ B ψ hB) := by sorry
