-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_one_self_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_one_self_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/a53113e9-a760-58ea-a01d-8c9111e7d648
-- title:
--   Identity of GL₂(K₀) acts trivially on G-points
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$, a commutative $\mathcal O$-algebra $O_{nr}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, a field $K_0$ that is an $\mathcal O$-algebra, a ring homomorphism $\iota$ from $\mathbb Z_{r^2}$ (the Witt vectors of the field with $r^2$ elements) to $O_{nr}$, a formal $\mathcal O_D$-module $\Phi$ over $O_{nr}/(r)$, a moduli package $M$ over $O_{nr}$, and a family $\eta$ assigning to each commutative ring $B$, each $\psi : O_{nr}\to B$ with $r$ nilpotent in $B$, and each rigidified object $(X,n,\rho)$ over $B$ a point of $M$. Assume the three laws $h\eta$ for $\eta$ over Noetherian bases: $\eta$ identifies two admissible rigidified objects exactly when they are isomorphic; $\eta$ commutes with pushforward along ring maps compatible with the structure maps; and every point of $M.obj\,B$ becomes, over the away-localisations at a finite family generating the unit ideal of $B$, the image under $\eta$ of an admissible rigidified object. Finally let $E_0$ be a ring homomorphism from the centraliser of $\{\Phi.\mathrm{actEnd}\,a\}\cup\{\Phi.\mathrm{varpiEnd}\}$ to $M_2(K_0)$. Then for every commutative Noetherian $\mathcal O$-algebra $B$ and every point $x$ of the functor $G$ over $B$ (an $\mathcal O$-algebra map $O_{nr}\to B$ with $r$ nilpotent in $B$, together with a point of $M$), the relation `ModuliPackage.G.IsActBy` holds for the identity of $\mathrm{GL}_2(K_0)$ with $x$ on both sides: there are an endomorphism $e$ in the centraliser and exponents $k,m'$ with $E_0e=r^k\cdot 1$, the kernel of $e$ of degree $r^{2m'}$, and $x$ a translate of itself in the sense of the local lifting condition through $\eta$.
--
--   This is the reflexivity clause of the relation by which $\mathrm{GL}_2(K_0)$ acts, via $E_0$, on the points of Drinfeld's functor attached to a special formal $\mathcal O_D$-module; it is the statement that the identity matrix relates every point to itself. It is used in the construction of rigidifications of fake elliptic curves compatible with the Frobenius twist and the Atkin–Lehner quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_one_self_of_isNoetherianRing.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_one_self_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime] (𝒪 : Type) [CommRing 𝒪]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : ModuliPackage.GPoint 𝒪 M B),
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ 1 x x := by sorry
