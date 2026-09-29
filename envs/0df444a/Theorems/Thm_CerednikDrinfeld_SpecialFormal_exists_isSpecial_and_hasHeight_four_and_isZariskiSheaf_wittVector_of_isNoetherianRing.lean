-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/163dd6a0-40ad-5847-a1b7-c09ac6f8dda7
-- title:
--   A special height-4 formal mathcal O_D-module and its Drinfeld moduli sheaf
-- statement:
--   Let $r$ be a prime and let $k$ be an algebraically closed field of characteristic $r$, and write $W = \mathrm{WittVector}\ r\ k$ and $\mathbb Z_{r^2} = \mathrm{WittVector}\ r\ \mathbb F_{r^2}$. The assertion is that there exist: a ring homomorphism $\iota : \mathbb Z_{r^2} \to W$; a formal $\mathcal O_D$-module $\Phi$ over $W/(r)$, that is, a two-dimensional commutative formal group law together with an action of $\mathbb Z_{r^2}$ by endomorphisms of the law and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [r]$ and $\varpi\circ[a] = [\mathrm{Frob}\,a]\circ\varpi$; a proof that $\Phi$ is special for the reduction of $\iota$ modulo $(r)$, in the sense that the two eigen-submodules `lieZero` and `lieOne` of its tangent space are complementary and each invertible; a proof that $[r]$ on $\Phi$ has kernel of degree $r^4$; a moduli package $M$ in universe $0$ over $W$, i.e. sets $M(B,\psi)$ for commutative rings $B$ with $\psi : W \to B$ and $r$ nilpotent in $B$, with functorial transition maps, which is a Zariski sheaf in the sense of the definition `IsZariskiSheaf`; and maps $\eta_{B,\psi}$ from rigidified data $(X,n,\rho)$ over $B$ to $M(B,\psi)$, defined for all such $B$, subject to three laws in which the test algebras are Noetherian: (i) two rigidified data admissible for $(\iota,\psi)$ ($X$ special of height $4$ and $\rho$ an isogeny $\Phi_{B/(r)} \to X_{B/(r)}$ of height $4n$) have equal images under $\eta$ exactly when they are isomorphic in the sense of `IsIsomorphic`; (ii) $\eta$ commutes with base change along any $f : B \to B'$ with $f\circ\psi = \psi'$, applied to admissible data; (iii) every element of $M(B,\psi)$ is, after passage to localisations away from the members of some finite family $f : \mathrm{Fin}\,n \to B$ generating the unit ideal, the image under $\eta$ of an admissible rigidified datum over each such (Noetherian) localisation in which $r$ is nilpotent.
--
--   This packages the local input to the Čerednik–Drinfeld uniformisation: the existence over $W(k)$ of a $\mathbb Z_{r^2}$-structure and of a special formal $\mathcal O_D$-module of height $4$, together with Drinfeld's moduli functor of rigidified special formal $\mathcal O_D$-modules, presented as a Zariski sheaf whose points are locally classified, up to isomorphism, by admissible rigidifications. It is the edition of the statement in which the test algebras occurring in the three laws are Noetherian, and it feeds the construction of the quaternionic group action on the moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing
    (r : ℕ) [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k] :
    ∃ (ι : Zp2 r →+* WittVector r k)
      (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r (WittVector r k)) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB),
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [IsNoetherianRing B] [CommRing B'] [IsNoetherianRing B'] (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m) := by sorry
