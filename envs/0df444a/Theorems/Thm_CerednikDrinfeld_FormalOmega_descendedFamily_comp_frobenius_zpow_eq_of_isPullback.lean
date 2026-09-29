-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedFamily_comp_frobenius_zpow_eq_of_isPullback
-- name    : CerednikDrinfeld.FormalOmega.descendedFamily_comp_frobenius_zpow_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/7a1ca2a5-7631-5d35-9b9c-e0a17835e909
-- title:
--   Twisted equivariance of the descended family ρ₂
-- statement:
--   Fix a prime $r$ and a characteristic-zero discrete valuation domain $\mathcal O$ with uniformiser $\pi$ (irreducible, $\mathcal O$ being $(\pi)$-adically complete, $\#(\mathcal O/\pi)=r$ and $(r)=(\pi)$), together with a characteristic-zero domain $\mathcal O^{\mathrm{nr}}$ over $\mathcal O$ that is $(\pi)$-adically complete with $(\pi)$ maximal, each of whose elements satisfies a monic $\mathcal O$-polynomial modulo $\pi$ and in which every monic polynomial of positive degree has a root modulo $\pi$, carrying an $\mathcal O$-algebra automorphism $\mathrm{Fr}$ with $\mathrm{Fr}(x)\equiv x^{r} \pmod{\pi}$; let $K_0$ be a fraction field of $\mathcal O$ of characteristic zero, $v\!\det:\mathrm{GL}_2(K_0)\to\mathbb Z$ a homomorphism, $\sigma:G\to \mathrm{GL}_2(K_0)$ a homomorphism from a group $G$, $\Gamma\le G$ and $\Gamma'$ the subgroup consisting of the $\gamma\in\Gamma$ with $v\!\det(\sigma\gamma)$ even. Let $t:T\to\operatorname{Spec}\mathcal O$ be a scheme over $\mathcal O$, and write $\mathcal O_2$ for the equaliser subalgebra of $\mathrm{Fr}^2$ and the identity on $\mathcal O^{\mathrm{nr}}$. Assume given: a family $\rho'$ assigning to each $\pi$-nilpotent $\mathcal O$-algebra $B$ a map from pairs $(\psi:\mathcal O^{\mathrm{nr}}\to_{\mathcal O} B,\,P$ a Deligne datum over $B)$ to the $B$-points of $T$ over $\mathcal O$, natural in $B$ and invariant under the twisted $\Gamma$-action (if $\gamma\in\Gamma$ and $x'$ has first component the $(-v\!\det(\sigma\gamma))$-th `frobTwist` of that of $x$ while its Deligne datum is the `DeligneDatum.IsPullback` of that of $x$ along $(\sigma\gamma)^{-1}$, then $\rho'$ agrees on $x$ and $x'$); and a family $\rho_2$ on pairs $(\psi_2:\mathcal O_2\to_{\mathcal O}B,\,P)$, natural in $B$, with $\rho_2(\psi|_{\mathcal O_2},P)=\rho'(\psi,P)$, and unique among natural families with this restriction property. Finally fix $n$ and an $\mathcal O$-algebra automorphism $\mathrm{Fr}_2$ of $\mathcal O_2/\pi^{n+1}$ induced by $\mathrm{Fr}$, in the sense that $\mathrm{Fr}_2(\bar y)=\overline{y'}$ whenever $y,y'\in\mathcal O_2$ satisfy $y'=\mathrm{Fr}(y)$. The conclusion is a conjunction. First: for every $\mathcal O$-algebra $B$ with $\pi^{n+1}=0$ in $B$, every $c:\mathcal O_2/\pi^{n+1}\to_{\mathcal O}B$, every $\gamma\in\Gamma$ and all Deligne data $P,P'$ over $B$ with $P'$ the pullback of $P$ along $(\sigma\gamma)^{-1}$, one has $\rho_2(c\circ \mathrm{Fr}_2^{-v\!\det(\sigma\gamma)}\circ(\mathcal O_2\to\mathcal O_2/\pi^{n+1}),P')=\rho_2(c\circ(\mathcal O_2\to\mathcal O_2/\pi^{n+1}),P)$. Second: for every $\pi$-nilpotent $B$, every $\psi_2:\mathcal O_2\to_{\mathcal O}B$, and every $g\in\mathrm{GL}_2(K_0)$ whose class in $\mathrm{PGL}_2(K_0)$ equals the class of $\sigma\gamma'$ for some $\gamma'\in\Gamma'$, and all $P,P'$ with $P'$ the pullback of $P$ along $g^{-1}$, one has $\rho_2(\psi_2,P')=\rho_2(\psi_2,P)$.
--
--   This records the equivariance properties of the family descended from $\hat{\mathcal O}^{\mathrm{nr}}$ to the subring fixed by $\mathrm{Fr}^2$, in the setting of the Čerednik–Drinfeld uniformisation: the first clause expresses that translating the Deligne datum by $\sigma\gamma$ is compensated by a power of Frobenius on the coefficient ring, and the second that the even part $\Gamma'$ acts trivially through $\mathrm{PGL}_2$. It is used in the construction of the quotient map from the descended family, `descendedQuotientMap_univ`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_descendedFamily_comp_frobenius_zpow_eq_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.descendedFamily_comp_frobenius_zpow_eq_of_isPullback
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B)
    (hρ'nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x))
    (hρ'inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x)
    (ρ₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B)
    (hρ₂nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
      ρ₂ B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ₂ B hB x))
    (hρ₂hon : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
      ρ₂ B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P))
    (hρ₂uniq : ∀ ρ₂' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
        ρ₂' B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ₂' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
        ρ₂' B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P)) →
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
        ρ₂' B hB x = ρ₂ B hB x)

    (n : ℕ) (Fr₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) → Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (γ : G), γ ∈ Γ →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P' →
        ρ₂ B ⟨n + 1, hB⟩ ((c.comp (Fr₂ ^ (- Multiplicative.toAdd (vdet (σ γ)))).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P') =
          ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ₂ : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] B)
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
      (∃ γ' ∈ Γ', Matrix.ProjGenLinGroup.mk (σ γ') = Matrix.ProjGenLinGroup.mk g) →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
        ρ₂ B hB (ψ₂, P') = ρ₂ B hB (ψ₂, P)) := by sorry
