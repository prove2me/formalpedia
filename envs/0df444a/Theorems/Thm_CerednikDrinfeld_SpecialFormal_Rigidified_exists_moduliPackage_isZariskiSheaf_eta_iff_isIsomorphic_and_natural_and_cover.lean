-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a6a2e5dd-f12e-5cb9-af89-83133d2067a3
-- title:
--   Existence of a Drinfeld moduli package for rigidified special formal O_D-modules
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ (a commutative two-dimensional formal group law together with a $\mathbb{Z}_{p^2}$-action and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[a^{\sigma}]\circ\varpi$) which is special relative to $\mathbb{Z}_{p^2}\to W(k)\to W(k)/pW(k)$, i.e. its two Lie summands are complementary and each invertible, and of height $4$, i.e. $[p]$ has kernel of degree $p^4$. The assertion is that there exist a moduli package $M$ over $W(k)$ — assigning to each commutative ring $B$ with a ring homomorphism $\psi\colon W(k)\to B$ and $p$ nilpotent in $B$ a type $M.obj\,B\,\psi$, with transition maps along ring homomorphisms compatible with the structure maps, functorial for identities and composites — which is a Zariski sheaf (separated and glueing for finite families generating the unit ideal, via localisations away from the $f_i$ and the $f_if_j$), together with maps $\eta$ sending a rigidified object $t=(X,n,\rho)$ over any such $B$ (a formal $O_D$-module $X$ over $B$, an integer $n$, and a pair of power series $\rho$ over $B/pB$) to an element of $M.obj\,B\,\psi$, subject to three conditions over Noetherian base rings: (i) for admissible $t,t'$ over $B$ (meaning $X$ special for the structure map attached to $\iota,\psi$, of height $4$, and $\rho$ an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$), $\eta(t)=\eta(t')$ holds precisely when $t$ and $t'$ are isomorphic in the sense of mutually inverse $O_D$-homomorphisms matching the rigidifications after a $p$-power twist; (ii) $\eta$ is natural: for $f\colon B\to B'$ with $f\circ\psi=\psi'$ and $t$ admissible, $\eta(t\cdot f)$ is the image of $\eta(t)$ under $M$; (iii) every $m\in M.obj\,B\,\psi$ is locally represented: there are finitely many $f_i\in B$ generating the unit ideal such that over every localisation $L$ of $B$ away from $f_i$ which is Noetherian with $p$ nilpotent there is an admissible rigidified $t$ over $L$ with $\eta(t)$ the image of $m$. Note that $\eta$ is provided for all base rings, while (i)–(iii) are asserted only for Noetherian ones.
--
--   This is the existence of Drinfeld's moduli functor for special formal $O_D$-modules of height $4$ with rigidification, realised as the Zariski sheafification of the presheaf of admissible rigidified objects modulo isomorphism, in the form used by Boutot–Carayol and Rapoport–Zink. It supplies the abstract pair $(M,\eta)$ on which the statements about Cartier quadruples and the period morphism in the Čerednik–Drinfeld uniformisation are built.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    :
    ∃ (M : ModuliPackage.{0, 0} p (WittVector p k)) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB),
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
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
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m) := by sorry
