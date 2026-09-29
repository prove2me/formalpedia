-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isPullback_of_isTranslate_of_isTranslate_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/401c3208-6a72-57e6-bc56-2e9cf3b195dc
-- title:
--   Period of an e-translate is a pullback along E(e)
-- statement:
--   Fix a prime $r$, an algebraically closed field $k$ of characteristic $r$, and a $\mathbb{Z}_r$-algebra structure on the Witt ring $W(k)$; let $\mathrm{Fr}$ be a $\mathbb{Z}_r$-algebra automorphism of $W(k)$ acting as the Witt vector Frobenius, $\iota : W(\mathbb{F}_{r^2}) \to W(k)$ a ring homomorphism, and $\Phi$ a formal $\mathcal{O}_D$-module over $W(k)/rW(k)$ whose multiplication by $r$ has kernel algebra finite projective of degree $r^4$. Let $M$ be a moduli package over $W(k)$, $\eta$ a family of maps from rigidified triples $(X,n,\rho)$ over $B$ to $M$-points which, over Noetherian $B$, identifies two $\psi$-admissible triples exactly when they are isomorphic, $\theta$ a family of maps from $M$-points to Deligne data over $B$ for $\mathbb{Q}_r$ and $\pi = r$, and $E$ a ring homomorphism from the centraliser of the $\mathcal{O}_D$-action endomorphisms $\Phi.\mathrm{actEnd}$ and $\Phi.\mathrm{varpiEnd}$ into $M_2(\mathbb{Q}_r)$. Assume two clauses over Noetherian test rings: $\mathrm{hGLdef}$, existence, for each admissible $t$ and each $e$ in that centraliser with kernel degree $r^{2m'}$, of an $e$-translate $t'$ on the same underlying $X$, admissible for $\psi\circ\mathrm{Frob}^{m'}$; and $\mathrm{hGLeq}$, that for such a pair the Deligne datum of $t'$ is the pullback along any $g$ with matrix $E(e)$ of that of $t$. Then for a Noetherian $\mathbb{Z}_r$-algebra $L$ with $r$ nilpotent, $\psi : W(k)\to L$, such an $e$ with kernel degree $r^{2m'}$, natural numbers $kk, m'$, any $g_0 \in \mathrm{GL}_2(\mathbb{Q}_r)$ with matrix $E(e)$, and rigidified $t$ admissible for $\psi$ and $t'$ admissible for $\psi\circ\mathrm{Fr}^{m'-2kk}$ with $\mathrm{Rigidified.IsTranslate}$ relating $t$ and $t'$ via $e$, $kk$ and $m'$ (equal underlying modules together with the displayed identity of rigidifications twisted by $r^{kk}$ and by the $r^{2kk}$-power Frobenius series), the Deligne datum $\theta(\eta(t'))$ equals, at every full $\mathbb{Z}_r$-lattice $N$ in $\mathbb{Q}_r^2$, the preimage of the line of $\theta(\eta(t))$ at $g_0 N$ under the base-changed action of $g_0$.
--
--   This is the compatibility of Drinfeld's period morphism with the action of the elements $r^{kk}E(e)^{-1}$ of $\mathrm{GL}_2(\mathbb{Q}_r)$ on the functor of rigidified special formal $\mathcal{O}_D$-modules, in the form given by Boutot–Carayol; it reduces the case of a general $kk$-fold translate to the untwisted case assumed in the hypothesis $\mathrm{hGLeq}$, the central factor $r^{kk}$ acting trivially on Deligne data by homothety invariance. It feeds the statement characterising when a group element acts on the moduli package as a twisted action of Frobenius type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isPullback_of_isTranslate_of_isTranslate_zero
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
      (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∃ t' : Rigidified r Φ B,
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
          t'.X = t.X ∧
          ∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))

    (hGLeq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
      (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
      ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
        t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
        t'.X = t.X →
        (∃ c : ℕ,
            (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
              (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
        DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
          (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
            (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t')))

    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e)
    (t t' : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι
      (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
        WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)))
    (htt' : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t') :
    DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL
        (η L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL t')) := by sorry
