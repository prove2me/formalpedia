-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/1f21c3a8-d3fa-5be2-8675-f23c3636741c
-- title:
--   Injectivity of the moduli sheaf on Noetherian fibre products
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to W(k)$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ (a two-dimensional commutative formal group law together with a $\mathbb{Z}_{p^2}$-action and a uniformiser endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[a^{\sigma}]\circ\varpi$), assumed special, i.e. its Lie algebra is the direct sum of the weight-$\iota$ and weight-$\iota^{\sigma}$ eigenmodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$, both invertible, with respect to the reduction of $\iota$, and of height $4$, i.e. the kernel of $[p]$ is finite projective of degree $p^4$ with all fibre dimensions $p^4$. Let $M$ be a moduli package over $W(k)$, that is, a functor $B\mapsto M(B)$ on commutative rings $B$ in `Type` equipped with a structure map $\psi\colon W(k)\to B$ and with $p$ nilpotent, and assume $M$ satisfies the Zariski sheaf condition (separatedness and glueing for finite covers by basic localisations). Let $\eta$ assign to each such $B$ and each rigidified datum $t=(X,n,\rho)$ over $B$ (a formal $O_D$-module $X$ over $B$, an integer $n$, and a series $\rho$ over $B/pB$) an element $\eta_B(t)\in M(B)$, and assume the three conditions: on Noetherian $B$, $\eta_B(t)=\eta_B(t')$ for admissible $t,t'$ (meaning $X$ special of height $4$ and $\rho$ an isogeny $\overline{\Phi}\to\overline{X}$ of height $4n$) precisely when $t$ and $t'$ are isomorphic as rigidified data; $\eta$ is natural along homomorphisms of Noetherian rings over $W(k)$ applied to admissible data; and every element of $M(B)$, for $B$ Noetherian, is, on the members of some finite cover of $B$ by localisations $B[1/f_i]$ with the $f_i$ generating the unit ideal, the image of an admissible rigidified datum under $\eta$. Now let $B,B',B''$ be Noetherian rings with structure maps $\psi,\psi',\psi''$ and $p$ nilpotent in each, and let $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ be surjective homomorphisms compatible with the structure maps and with nilpotent kernels. Let $P=B'\times_B B''$ be the subring of $B'\times B''$ on which $\varphi'$ and $\varphi''$ agree, assume $p$ is nilpotent in $P$, and let $\psi_P\colon W(k)\to P$ be a structure map whose compositions with the two projections are $\psi'$ and $\psi''$. Then for $z_1,z_2\in M(P)$ whose images in $M(B')$ under the first projection agree and whose images in $M(B'')$ under the second projection agree, one has $z_1=z_2$.
--
--   This is the injectivity (uniqueness) half of the fibre-product exactness of Drinfeld's moduli functor on Noetherian corners, as in Boutot–Carayol II (10.2): the map $M(B'\times_B B'')\to M(B')\times M(B'')$ is injective under the stated hypotheses on the surjections. It is isolated from the combined statement because the existence half of that result invokes it on the overlaps of a Zariski cover; it is used by [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf) and by the corresponding `existsUnique` form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
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
    (z₁ z₂ : M.obj (ModuliPackage.pullbackRing φ' φ'') ψP hP)
    (h' : M.map hP hB' (ModuliPackage.pullbackFst φ' φ'') hψP' z₁ =
      M.map hP hB' (ModuliPackage.pullbackFst φ' φ'') hψP' z₂)
    (h'' : M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'') hψP'' z₁ =
      M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'') hψP'' z₂) :
    z₁ = z₂ := by sorry
