-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/e7a2c768-69df-548e-8315-c9dd84e58175
-- title:
--   Gluing M along fibre squares of Noetherian rings: existence
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to W(k)$, and a formal $O_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for the structure map obtained from $\iota$ by reduction (its zero and one Lie eigen-submodules are complementary and each invertible) and has height $4$ (the kernel of its action of $p$ has degree $p^4$). Let $M$ be a moduli package over $W(k)$, i.e. a functorial assignment $B\mapsto M(B)$ on commutative rings $B$ equipped with a map $W(k)\to B$ and with $p$ nilpotent, assumed to satisfy the Zariski sheaf condition `IsZariskiSheaf` (separation and gluing for finite covers by localisations away from elements generating the unit ideal), and let $\eta$ send rigidified data $(X,n,\rho)$ over $B$ to elements of $M(B)$, subject to three conditions on Noetherian rings: $\eta$ identifies two admissible rigidified objects precisely when they are isomorphic; $\eta$ is compatible with base change along ring maps over $W(k)$; and every element of $M(B)$ becomes, after localising away from each member of some finite family generating the unit ideal of $B$, of the form $\eta(t)$ for an admissible $t$. Let further $B,B',B''$ be Noetherian rings with maps $\psi,\psi',\psi''$ from $W(k)$ and $p$ nilpotent in each, and let $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ be surjective homomorphisms over $W(k)$ with nilpotent kernels. Write $P=\{(b',b'')\in B'\times B'' : \varphi'(b')=\varphi''(b'')\}$ for `pullbackRing`, assume $p$ nilpotent in $P$, and let $\psi_P\colon W(k)\to P$ be a structure map whose composites with the two projections are $\psi'$ and $\psi''$. Then for all $x'\in M(B')$ and $x''\in M(B'')$ with the same image in $M(B)$ there exists $z\in M(P)$ whose images under the two projections are $x'$ and $x''$.
--
--   This is the existence half of the exactness of Drinfeld's moduli sheaf on fibre squares of Noetherian rings with $p$ nilpotent, as in Boutot–Carayol, chapter II (10.2). Combined with the corresponding uniqueness statement it yields the unique-gluing form `existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
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
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))

    (ψP : WittVector p k →+* ModuliPackage.pullbackRing φ' φ'')
    (hψP' : (ModuliPackage.pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (ModuliPackage.pullbackSnd φ' φ'').comp ψP = ψ'')
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB'')
    (hx : M.map hB' hB φ' hφ' x' = M.map hB'' hB φ'' hφ'' x'') :
    ∃ z : M.obj (ModuliPackage.pullbackRing φ' φ'') ψP hP,
      M.map hP hB' (ModuliPackage.pullbackFst φ' φ'') hψP' z = x' ∧
      M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'') hψP'' z = x'' := by sorry
