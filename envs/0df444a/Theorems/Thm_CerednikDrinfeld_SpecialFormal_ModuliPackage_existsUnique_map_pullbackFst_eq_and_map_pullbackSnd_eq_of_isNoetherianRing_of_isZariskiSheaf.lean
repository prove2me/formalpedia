-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/77b00b95-00ae-5ee3-9072-26572747f637
-- title:
--   Fibre-product exactness of the moduli package over Noetherian rings
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ (a two-dimensional commutative formal group law with an action of $W(\mathbb F_{p^2})$ and a uniformiser series $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$) which is special for the reduction of $\iota$ — its Lie algebra is the direct sum of the $\iota$-eigenspace and the $\sigma\iota$-eigenspace, both invertible — and has height $4$, meaning the kernel algebra of $[p]$ is finite projective of fibre rank $p^4$. Let $M$ be a moduli package over $W(k)$, i.e. a functor $B\mapsto M(B)$ on $W(k)$-algebras with $p$ nilpotent, assumed to satisfy the Zariski sheaf condition `IsZariskiSheaf`, and let $\eta$ assign to each rigidified triple over such a $B$ an element of $M(B)$, subject to three conditions on Noetherian $B$: $\eta$ identifies two admissible triples exactly when they are isomorphic, $\eta$ is compatible with base change along maps of Noetherian algebras, and every element of $M(B)$ becomes an $\eta$-image of an admissible triple over each member of some Noetherian Zariski cover of $B$ by localisations away from a finite family generating the unit ideal. Then for all Noetherian $W(k)$-algebras $B,B',B''$ with $p$ nilpotent, surjections $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ over $W(k)$ with nilpotent kernels, $p$ nilpotent in the fibre product $B'\times_B B''$ (realised as the equaliser subring of $B'\times B''$), and elements $x'\in M(B')$, $x''\in M(B'')$ with the same image in $M(B)$, there is a unique $z\in M(B'\times_B B'')$, for the induced structure map, whose images under the two projections are $x'$ and $x''$.
--
--   This is the fibre-product exactness property of the moduli package — the analogue of Schlessinger's conditions (H1)–(H2) for the Drinfeld moduli problem of special formal $\mathcal O_D$-modules — in the form restricted to Noetherian corners, which is what the frame with $\eta$ defined only over Noetherian algebras supports. It is used in the proof that a period map is bijective on Noetherian algebras when the Lie action of $\varpi$ vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    :
    (∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB''),
      M.map hB' hB φ' hφ' x' = M.map hB'' hB φ'' hφ'' x'' →
      ∃! z : M.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        M.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'') := by sorry
