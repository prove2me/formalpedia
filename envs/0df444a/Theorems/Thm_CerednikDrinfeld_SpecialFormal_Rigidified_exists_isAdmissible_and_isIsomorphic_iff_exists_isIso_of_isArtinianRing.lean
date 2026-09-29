-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a79ae494-f31f-57d8-b6fb-ff1cf80b359a
-- title:
--   Rigidifying deformations of a special formal mathcal O_D-module over Artinian bases
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, $\iota\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to O$ a ring homomorphism and $\Phi$ a formal $\mathcal O_D$-module over $O/pO$, i.e. a commutative $2$-dimensional formal group law with a $\mathbb Z_{p^2}$-action by law endomorphisms and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[a^{\sigma}]\circ\varpi$. Let $k$ be a field of characteristic $p$, $\psi_k\colon O\to k$ a ring homomorphism, and $t_0=(X_0,n_0,\rho_0)$ a rigidified object over $k$ (a formal $\mathcal O_D$-module $X_0$ over $k$, an integer $n_0$, and a $2$-tuple of power series $\rho_0$ over $k/pk$) which is admissible for $(\iota,\psi_k)$: $X_0$ is special for $\psi_k\circ\iota$ (its Lie module is the direct sum of the submodule where $\mathbb Z_{p^2}$ acts through $\psi_k\circ\iota$ and the one where it acts through the Frobenius twist, both invertible), $X_0$ has height $4$ (multiplication by $p$ has kernel of degree $p^4$), and $\rho_0$ is an $\mathcal O_D$-linear isogeny $\Phi_{k/p}\to (X_0)_{k/p}$ of height $4n_0$. Let $A$ be an Artinian local commutative ring, $\psi_A\colon O\to A$, and $\mathrm{res}\colon A\to k$ a surjective ring homomorphism with $\mathrm{res}\circ\psi_A=\psi_k$. Call a homomorphism $v\colon X_0\to X\otimes_{\mathrm{res}}k$ compatible with a rigidified object $t=(X,n,\rho)$ over $A$ if for some $m\ge 0$ one has $[p^{m+n}]\circ(\bar v\circ\rho_0)=[p^{m+n_0}]\circ\bar\rho$ as series over $k/pk$, the multiplications by $p^{m+\ast}$ being taken on the reduction of $X\otimes_{\mathrm{res}}k$ modulo $p$, and $\bar v$, $\bar\rho$ the reductions of the series of $v$ and of $\rho$. Five assertions are made simultaneously. (1) For every formal $\mathcal O_D$-module $X$ over $A$ that is special for $\psi_A\circ\iota$ and of height $4$, and every isomorphism $v\colon X_0\to X\otimes_{\mathrm{res}}k$, there are $n$ and $\rho$ such that $(X,n,\rho)$ is admissible for $(\iota,\psi_A)$ and $v$ is compatible with it. (2) For admissible $t,t'$ over $A$ and homomorphisms $v\colon X_0\to t.X\otimes_{\mathrm{res}}k$, $v'\colon X_0\to t'.X\otimes_{\mathrm{res}}k$ compatible with $t$ and $t'$ respectively, $t$ and $t'$ are isomorphic as rigidified objects (mutually inverse $\mathcal O_D$-homomorphisms of the underlying modules matching the rigidifications after multiplication by a power of $p$) if and only if there is an isomorphism $s\colon t.X\to t'.X$ with $v$ followed by $s\otimes_{\mathrm{res}}k$ equal to $v'$. (3) If $t$ is admissible and $t_0$ is isomorphic to $t\otimes_{\mathrm{res}}k$ as rigidified objects, then some isomorphism $v\colon X_0\to t.X\otimes_{\mathrm{res}}k$ is compatible with $t$. (4) Conversely, if $t$ is admissible and some isomorphism $v$ is compatible with $t$, then $t_0$ and $t\otimes_{\mathrm{res}}k$ are isomorphic in both directions. (5) For admissible $t$ over $A$, any Artinian local ring $A'$ with $\psi_{A'}\colon O\to A'$ and surjective $\mathrm{res}'\colon A'\to k$ satisfying $\mathrm{res}'\circ\psi_{A'}=\psi_k$, and any $f\colon A\to A'$ with $\mathrm{res}'\circ f=\mathrm{res}$ and $f\circ\psi_A=\psi_{A'}$, the base change $t\otimes_f A'$ is admissible for $(\iota,\psi_{A'})$, and if $v$ is compatible with $t$ and $v'\colon X_0\to (t\otimes_f A').X\otimes_{\mathrm{res}'}k$ has the same underlying series as $v$, then $v'$ is compatible with $t\otimes_f A'$.
--
--   This is the dictionary between the deformation theory of a height-$4$ special formal $\mathcal O_D$-module $X_0$ over $k$ along Artinian local thickenings and the formal fibre at $t_0$ of Drinfeld's functor of rigidified special formal $\mathcal O_D$-modules: admissible rigidifications exist and are unique up to isomorphism over the deformation, isomorphism of rigidified objects is detected by isomorphisms of the underlying modules commuting with the chosen identification over $k$, and everything is compatible with base change. It is used in the study of the period map attached to the moduli package, in particular by [`CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.eq_of_map_fstHom_eq_of_apply_eq_dualNumber_of_lieVarpi_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {k : Type u} [Field k] [CharP k p] (ψk : O →+* k)
    (t₀ : Rigidified p Φ k) (ht₀ : t₀.IsAdmissible ι ψk)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (ψA : O →+* A)
    (res : A →+* k) (hres : Function.Surjective res) (hψ : res.comp ψA = ψk) :

    (∀ (X : FormalODModule p A), X.IsSpecial (ψA.comp ι) → X.HasHeight 4 →
      ∀ (v : t₀.X.Hom (X.map res)), v.IsIso →
      ∃ (n : ℕ) (ρ : Series (A ⧸ pIdeal p A)),
        (⟨X, n, ρ⟩ : Rigidified p Φ A).IsAdmissible ι ψA ∧
        ∃ m : ℕ,
          (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp
              (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).ρ)) ∧

    (∀ (t t' : Rigidified p Φ A), t.IsAdmissible ι ψA → t'.IsAdmissible ι ψA →
      ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom (t'.X.map res)),
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      (∃ m : ℕ,
          ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp
              ((v'.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t'.map res).ρ) →
      (t.IsIsomorphic t' ↔
        ∃ s : t.X.Hom t'.X, s.IsIso ∧ (s.map res).comp v = v')) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA → t₀.IsIsomorphic (t.map res) →
      ∃ (v : t₀.X.Hom (t.X.map res)), v.IsIso ∧
        ∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA → ∀ (v : t₀.X.Hom (t.X.map res)), v.IsIso →
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      t₀.IsIsomorphic (t.map res) ∧ (t.map res).IsIsomorphic t₀) ∧

    (∀ (t : Rigidified p Φ A), t.IsAdmissible ι ψA →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] (ψA' : O →+* A')
        (res' : A' →+* k), Function.Surjective res' → res'.comp ψA' = ψk →
      ∀ (f : A →+* A'), res'.comp f = res → f.comp ψA = ψA' →
        (t.map f).IsAdmissible ι ψA' ∧
        ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom ((t.map f).X.map res')),
          v'.toSeries = v.toSeries →
          (∃ m : ℕ,
              ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp
                  ((v.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
                ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
          ∃ m : ℕ,
            (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + (t.map f).n))).comp
                ((v'.toSeries.map (Ideal.Quotient.mk (pIdeal p k))).comp t₀.ρ) =
              (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp ((t.map f).map res').ρ) := by sorry
