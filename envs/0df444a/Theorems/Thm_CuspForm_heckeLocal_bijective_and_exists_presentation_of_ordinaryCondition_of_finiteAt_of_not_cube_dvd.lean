-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd
-- name    : CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/3dd36671-b1b8-54b4-ab1c-3e66b850156a
-- title:
--   R=T and complete intersection at cube-free ordinary level
-- statement:
--   Fix an odd prime $p$ and a Weierstrass model $W$ over $\mathbb{Z}$ with $\Delta(W)\neq 0$ which is semistable in the sense that no prime dividing $\Delta(W)$ divides $c_4(W)$, and whose mod $p$ representation is irreducible: the $p$-torsion of $W$ over $\overline{\mathbb{Q}}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and the whole module. Let $\mathcal{O}'$ be a characteristic-zero complete discrete valuation ring with finite residue field and $p$ in its maximal ideal. Let $S$ be a finite set of primes containing $p$ and every prime dividing $\Delta(W)$, and let $N$ be a level all of whose prime divisors lie in $S$, with $q^{2}\mid N$ and $q^{3}\nmid N$ for every $q\in S$ with $q\neq p$, and $p\parallel N$; the space $S_2(\Gamma_0(N))$ is assumed to be spanned over $\mathbb{C}$ by its forms with integral $q$-expansion coefficients. Assume $W$ has good reduction at $p$ ($p\nmid\Delta(W)$) or is peu ramifiée at $p$ ($p\mid v_p(\Delta)$ over $\mathbb{Q}$), that the $p$-torsion over $\overline{\mathbb{Q}}$ has cardinality $p^{2}$ and that the mod $p$ representation is trivial on the Galois group of a finite extension, so that the residual representation $\bar\rho$ over $\mathbb{Z}/p$ is defined; let $\iota\colon\mathbb{Z}/p\to k'$ be a ring map into the residue field of $\mathcal{O}'$ such that every Frobenius characteristic polynomial of $\bar\rho\otimes_\iota k'$ splits into linear factors over $k'$. Assume further the Taylor–Wiles irreducibility hypothesis: over every field extension $K$ of $k'$, every subspace of $(\bar\rho\otimes_\iota k')\otimes K$ stable under some index-two subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is $0$ or everything. Flat auxiliary data are given: a squarefree level $N_{\mathrm{ft}}$ prime to $p$ dividing $N/p$, whose prime divisors lie in $S$ and whose primes $q\neq p$ are exactly those at which $\bar\rho$ ramifies, at which $W$ is residually modular (there is a normalised eigenform of weight $2$ and level $N_{\mathrm{ft}}$ and a maximal ideal $\mathfrak{m}$ of $\overline{\mathbb{Z}}$ containing $p$ with $a_\ell\equiv a_\ell(W)$ for good $\ell\nmid N_{\mathrm{ft}}$, $\ell\neq p$), together with a character $\theta_{\mathrm{ft}}$ of the weight-$2$ level-$N_{\mathrm{ft}}$ Hecke algebra outside $S$ sending $T_\ell$ to the residue of $a_\ell(W)$, the corresponding integral structure at level $N_{\mathrm{ft}}$, and an $\mathcal{O}'$-algebra point $\pi_{\mathrm{ft}}$ of [`CuspForm.heckeLocal Nft S 𝒪' θft`](def/CuspForm_HeckeLocal.html#L131). At level $N$ are given the analogous character $\theta_1$ with $\theta_1(T_\ell)=$ residue of $a_\ell(W)$, a datum [`CuspForm.HeckeGaloisRepDatum`](def/CuspForm_HeckeGaloisRepDatum.html#L8) on $\mathbb{T}:=$ [`CuspForm.heckeLocal N S 𝒪' θ₁`](def/CuspForm_HeckeLocal.html#L131) (a Hecke algebra map $\pi$ lifting $\theta_1$, generating $\mathbb{T}$ over $\mathcal{O}'$, interpolating $\mathcal{O}'$-valued eigensystems, together with a rank-two adic representation with Frobenius characteristic polynomials $X^{2}-\pi(T_\ell)X+\ell$ and absolutely irreducible residual representation), a deformation ring datum $D$ for $\bar\rho\otimes_\iota k'$ and the condition [`GaloisRep.ordinaryCondition 𝒪' p S`](def/GaloisRep_LocalConditions.html#L28) (cyclotomic determinant, ordinarity at $p$, unramifiedness outside $S$), and a local $\mathcal{O}'$-algebra map $\varphi\colon D.R\to\mathbb{T}$ whose base-changed universal representation is equivalent to the one carried by $H$. Then $\varphi$ is bijective, and there are $n$ and $f\colon \mathrm{Fin}\,n\to\mathcal{O}'[[X_1,\dots,X_n]]$ with $\mathcal{O}'[[X_1,\dots,X_n]]/(f_1,\dots,f_n)$ isomorphic to $\mathbb{T}$ as an $\mathcal{O}'$-algebra.
--
--   This is the $R=T$ step of the Taylor–Wiles argument in the ordinary Selmer-type case at a level exactly divisible by $p$, with the additional restriction that $N$ is cube-free away from $p$: the realising map from the universal ordinary deformation ring to the local Hecke ring is an isomorphism and that Hecke ring is a complete intersection over $\mathcal{O}'$. It feeds the two results that build patching data for residually modular semistable curves on the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial in
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in

theorem CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')] [CharZero 𝒪']
    (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (N : ℕ) [NeZero N]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNS2 : ∀ q ∈ S, q ≠ p → q ^ 2 ∣ N)
    (hN3 : ∀ q ∈ S, q ≠ p → ¬ q ^ 3 ∣ N)
    (hpN : p ∣ N) (hp2N : ¬ p ^ 2 ∣ N)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (hfin : W.IsGoodPrimeFor p ∨ (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p))
    (ι : ZMod p →+* IsLocalRing.ResidueField 𝒪')
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ α β : IsLocalRing.ResidueField 𝒪',
      LinearMap.charpoly ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι).ρ σ) =
        (X - C α) * (X - C β))

    (hTW : ∀ (K : Type) [Field K] [Algebra (IsLocalRing.ResidueField 𝒪') K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι).baseChange K).V),
        (∀ σ ∈ G, ∀ x ∈ V, ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι).baseChange K).ρ σ x ∈ V) →
        V = ⊥ ∨ V = ⊤)

    (Nft : ℕ) [NeZero Nft] [Fact (CuspForm.HasIntegralStructure Nft 2)]
    (hsqft : Squarefree Nft)
    (hramft : ∀ q : ℕ, q.Prime → q ≠ p →
      (q ∣ Nft ↔ ¬ ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q))
    (hpNft : ¬ p ∣ Nft) (hresft : W.IsResiduallyModularOfLevel p Nft)
    (hNftN : Nft ∣ N / p) (hNftS : ∀ q : ℕ, q.Prime → q ∣ Nft → q ∈ S)
    (θft : CuspForm.heckeAlgebra Nft 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪')
    (hθft : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ Nft) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      θft (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪' ((W.apOfModel ℓ : ℤ) : 𝒪'))
    (πft : CuspForm.heckeLocal Nft (↑S : Set ℕ) 𝒪' θft →ₐ[𝒪'] 𝒪')

    (θ₁ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪')
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪' ((W.apOfModel ℓ : ℤ) : 𝒪'))
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪' θ₁ (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁))
    (D : GaloisRep.DeformationRingData 𝒪'
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι)
      (GaloisRep.ordinaryCondition 𝒪' p S))
    (φ : D.R →ₐ[𝒪'] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁)
    (hφ : IsLocalHom (φ : D.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁))
    (heq : (D.ρ.baseChangeAlong (φ : D.R →+* CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁) hφ).IsEquiv H.ρ) :
    Function.Bijective φ ∧
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪'),
        Nonempty ((MvPowerSeries (Fin n) 𝒪' ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪'] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁) := by sorry
