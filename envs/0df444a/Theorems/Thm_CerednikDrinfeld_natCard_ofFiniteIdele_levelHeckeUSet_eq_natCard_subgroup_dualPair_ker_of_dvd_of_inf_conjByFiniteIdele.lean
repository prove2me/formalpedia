-- Prove2me | Theorems.Thm_CerednikDrinfeld_natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele
-- name    : CerednikDrinfeld.natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/82219150-5040-51b9-a2c4-0c29fd0ba7bf
-- title:
--   Brandt U_ℓ count at a prime dividing the level
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic a prime $q'$ which is algebraic over $\mathbb{Z}/q'$, and let $X_1$ be an elliptic Weierstrass curve over $\kappa$ with no nonzero $q'$-torsion point. Let $a,b\in\mathbb{Q}$ satisfy `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$ tensored with the completion at $v$ has all nonzero elements invertible exactly when $q'\in v$. Let $\Lambda_1\subseteq\mathbb{H}$ be a maximal order (a $\mathbb{Z}$-submodule containing $1$, closed under multiplication, spanning $\mathbb{H}$ over $\mathbb{Q}$, finitely generated, and maximal among such), and let $\theta_1$ be an injective ring homomorphism from the subring of rational endomorphisms of $X_1$ onto $\Lambda_1$. Let $N\neq 0$ with $q'\nmid N$, and let $m$ be a unit of $\mathbb{H}\otimes_{\mathbb{Q}}\widehat{\mathbb{Q}}$ (finite adeles) with $m$ and $N\,m^{-1}$ in the adelic box $\widehat{\Lambda_1}$, such that the conjugate order $\mathbb{H}\cap m\widehat{\Lambda_1}m^{-1}$ is maximal; put $R=\Lambda_1\cap(\mathbb{H}\cap m\widehat{\Lambda_1}m^{-1})$ and assume the relative index of $R$ in $\Lambda_1$ as additive groups is $N$. Let $\ell$ be a prime with $\ell\neq q'$ and $\ell\mid N$, and let $x,y$ be units of $\mathbb{H}\otimes\widehat{\mathbb{Q}}$. Assume given, for $x$: an elliptic curve $W_x$, a nonzero rational homomorphism $\chi_x\colon X_1\to W_x$, a unit $d_x\in\mathbb{H}^{\times}$ with $\theta_1$ of the kernel-ideal set of $\chi_x$ equal to the quaternion conjugate of $d_x\cdot(\mathbb{H}\cap x\widehat{\Lambda_1})$, an elliptic curve $W_x'$ and rational homomorphisms $\psi_x\colon W_x\to W_x'$, $\psi_x'\colon W_x'\to W_x$ with $\psi_x'\psi_x=N$ and $\psi_x\psi_x'=N$, with $\ker\psi_x$ cyclic of order $N$, and with $\theta_1$ of the kernel-ideal set of $\psi_x\circ\chi_x$ equal to the conjugate of $d_x\cdot(\mathbb{H}\cap xm\widehat{\Lambda_1})$; and the same data $W_y,\chi_y,d_y,W_y',\psi_y,\psi_y'$ for $y$. Then the number of $\mathbb{Z}$-submodules $J$ of $\mathbb{H}$ that are of the form $\mathbb{H}\cap xh\widehat{R}$ for some $h\in$ `levelHeckeUSet` $\Lambda_1\,R\,\ell$ — that is, $h$ lies in the $\ell$-Hecke set of $R$ ($h\in\widehat R$, $\ell h^{-1}\in\widehat R$, $h^{-1}\notin\widehat R$, $\ell^{-1}h\notin\widehat R$), $\mathbb{H}\cap h\widehat Rh^{-1}\neq R$ and $R\not\leq\mathbb{H}\cap h\widehat{\Lambda_1}h^{-1}$ — and which in addition satisfy $J=c\,(\mathbb{H}\cap y\widehat{R})$ for some $c\in\mathbb{H}^{\times}$, equals the number of subgroups $D$ of $W_x(\kappa)$ of order $\ell$ for which there exist rational homomorphisms $\varphi\colon W_x\to W_y$ and $\varphi'\colon W_y\to W_x$ with $\ker\varphi=D$, $\varphi'\varphi=\ell$, $\varphi\varphi'=\ell$, $\varphi(\ker\psi_x)\subseteq\ker\psi_y$, and $\varphi$ injective on $\ker\psi_x$.
--
--   This is the Brandt-matrix dictionary at a prime dividing the level: it identifies the adelic $U_\ell$-Hecke count between two classes of the Eichler-type order $R=\Lambda_1\cap m\widehat{\Lambda_1}m^{-1}$ with the count of order-$\ell$ subgroups of $W_x$ giving dual-pair $\ell$-isogenies $W_x\to W_y$ that carry the level-$N$ cyclic subgroup $\ker\psi_x$ injectively into $\ker\psi_y$, the extra injectivity conjunct being what distinguishes $\ell\mid N$ from the good-prime case. It is used in the comparison of the supersingular Hecke matrix with the class-set Hecke matrix at primes dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

theorem CerednikDrinfeld.natCard_ofFiniteIdele_levelHeckeUSet_eq_natCard_subgroup_dualPair_ker_of_dvd_of_inf_conjByFiniteIdele
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q') (hℓN : ℓ ∣ N)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (Wx : WeierstrassCurve κ) [Wx.IsElliptic] (χx : X₁.toAffine.Point →+ Wx.toAffine.Point)
    (hχx : χx ∈ WeierstrassCurve.rationalHomSet κ X₁ Wx) (hχx0 : χx ≠ 0) (dx : (ℍ[ℚ, a, b])ˣ)
    (hKx : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ Wx χx =
      star '' ((dx • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (Wx' : WeierstrassCurve κ) [Wx'.IsElliptic] (ψx : Wx.toAffine.Point →+ Wx'.toAffine.Point)
    (hψx : ψx ∈ WeierstrassCurve.rationalHomSet κ Wx Wx')
    (ψx' : Wx'.toAffine.Point →+ Wx.toAffine.Point) (hψx' : ψx' ∈ WeierstrassCurve.rationalHomSet κ Wx' Wx)
    (hψxd : ψx'.comp ψx = (N : ℕ) • AddMonoidHom.id _) (hψxd' : ψx.comp ψx' = (N : ℕ) • AddMonoidHom.id _)
    (hKx' : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ Wx' (ψx.comp χx) =
      star '' ((dx • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hψxc : IsAddCyclic ψx.ker) (hψxN : Nat.card ψx.ker = N)
    (Wy : WeierstrassCurve κ) [Wy.IsElliptic] (χy : X₁.toAffine.Point →+ Wy.toAffine.Point)
    (hχy : χy ∈ WeierstrassCurve.rationalHomSet κ X₁ Wy) (hχy0 : χy ≠ 0) (dy : (ℍ[ℚ, a, b])ˣ)
    (hKy : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ Wy χy =
      star '' ((dy • Submodule.ofFiniteIdele Λ₁ y : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (Wy' : WeierstrassCurve κ) [Wy'.IsElliptic] (ψy : Wy.toAffine.Point →+ Wy'.toAffine.Point)
    (hψy : ψy ∈ WeierstrassCurve.rationalHomSet κ Wy Wy')
    (ψy' : Wy'.toAffine.Point →+ Wy.toAffine.Point) (hψy' : ψy' ∈ WeierstrassCurve.rationalHomSet κ Wy' Wy)
    (hψyd : ψy'.comp ψy = (N : ℕ) • AddMonoidHom.id _) (hψyd' : ψy.comp ψy' = (N : ℕ) • AddMonoidHom.id _)
    (hKy' : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ Wy' (ψy.comp χy) =
      star '' ((dy • Submodule.ofFiniteIdele Λ₁ (y * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hψyc : IsAddCyclic ψy.ker) (hψyN : Nat.card ψy.ker = N) :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ levelHeckeUSet Λ₁ R ℓ, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ c : (ℍ[ℚ, a, b])ˣ, J = c • Submodule.ofFiniteIdele R y} =
      Nat.card {D : AddSubgroup Wx.toAffine.Point // Nat.card D = ℓ ∧
        ∃ φ ∈ WeierstrassCurve.rationalHomSet κ Wx Wy, ∃ φ' ∈ WeierstrassCurve.rationalHomSet κ Wy Wx,
          φ.ker = D ∧ φ'.comp φ = ℓ • AddMonoidHom.id _ ∧ φ.comp φ' = ℓ • AddMonoidHom.id _ ∧
          (∀ T ∈ ψx.ker, φ T ∈ ψy.ker) ∧ ∀ T ∈ ψx.ker, φ T = 0 → T = 0} := by sorry
