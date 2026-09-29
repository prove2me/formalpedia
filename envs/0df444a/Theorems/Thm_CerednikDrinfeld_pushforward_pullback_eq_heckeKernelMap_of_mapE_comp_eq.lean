-- Prove2me | Theorems.Thm_CerednikDrinfeld_pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq
-- name    : CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/e860274b-59fe-5d9a-a0d4-0de21bb30222
-- title:
--   Push-forward after pull-back is the class-set Hecke map at ℓ
-- statement:
--   Let $a,b\in\mathbb{Q}$ and $N,q,q'\in\mathbb{N}$ with $N\neq 0$ squarefree, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\geq 5$, and suppose $a<0$, $b<0$ and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q'\in v$. Let $\Lambda$ be a maximal $\mathbb{Z}$-order, $R\leq\Lambda$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$ in the first), and $n$ a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ in the $q$-th prime Hecke set of $R$, such that $\mathrm{meetOrder}\,R\,n=R\cap nRn^{-1}$ is Eichler of level $Nq$, is normalised by $n$, and the double shift by $n$ is the identity on the class set of the finite-idele stabiliser of $\mathrm{meetOrder}\,R\,n$; the class sets of the stabilisers of $R$ and of $\mathrm{meetOrder}\,R\,n$ are assumed finite. Let $\ell$ be a prime with $\ell\neq q$, $\ell\neq q'$, and $s$ a finite idele with $\hat{\ell}\,s^{-1}$ in the $\Lambda$-oriented level Hecke set $\mathrm{levelHeckeUSet}\,\Lambda\,(\mathrm{meetOrder}\,R\,n)\,\ell$ if $\ell\mid N$ and in the $\ell$-th prime Hecke set of $\mathrm{meetOrder}\,R\,n$ otherwise; assume $R\cap sRs^{-1}$ is Eichler of level $N\ell$, and let $n'$ lie in the $q$-th prime Hecke set of $R\cap sRs^{-1}$ with $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$ Eichler of level $N\ell q$, normalised by $n'$, with double shift by $n'$ the identity on the corresponding class set, and with $n^{-1}n'$ in the finite-idele stabiliser of $R$ and $sn'=n's$; the relevant class sets are again assumed finite. Finally let $D$ on finite types $E,V$ and $D''$ on finite types $E'',V''$ be degeneracy data (two maps $E\to V$ together with a positive width function on $E$), let $e_E$ and $e_{E''}$ be bijections of $E$, respectively $E''$, with the class sets of the stabilisers of $\mathrm{meetOrder}\,R\,n$, respectively of $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$, matching the widths of $D$ and $D''$ with the class weights of $\mathrm{classSetDegeneracyData}\,R\,n$ and $\mathrm{classSetDegeneracyData}\,(R\cap sRs^{-1})\,n'$, let $e$ be a $\mathbb{Z}$-linear isomorphism from the ribbon kernel of $D$ to that of $\mathrm{classSetDegeneracyData}\,R\,n$ given coefficientwise by transport along $e_E$, and let $\mu_0,\mu_1$ be finite homomorphisms $D''\to D$ whose edge maps correspond, through $e_{E''}$ and $e_E$, to the forgetful map of class sets and to the right shift $[\tilde x]\mapsto[\tilde x\,s]$. Then for every $z$ in the ribbon kernel of $\mathrm{classSetDegeneracyData}\,R\,n$ one has $e(\mu_{0*}(\mu_1^{*}(e^{-1}z)))=\mathrm{heckeKernelMap}\,(\mathrm{classSetHeckeData}\,N\,q\,\Lambda\,R\,n)\,\ell\,(z)$, that is, the composite of pull-back along $\mu_1$ (multiply the value at $\mu_1(\mathrm{edge})$ by the local degree) with push-forward along $\mu_0$ (sum over edge fibres) is, in the class-set coordinates, multiplication by the $\ell$-th edge Hecke matrix of the class-set Hecke data, namely the Hecke matrix of $\mathrm{levelHeckeUSet}\,\Lambda\,(\mathrm{meetOrder}\,R\,n)\,\ell$ when $\ell\mid N$ and of the $\ell$-th prime Hecke set of $\mathrm{meetOrder}\,R\,n$ otherwise.
--
--   This identifies the geometric correspondence on cycles of the dual graph of a totally degenerate covering — push-forward along the forgetful degeneracy map composed with pull-back along the shift by $s$ — with the Hecke operator $T_\ell$ (respectively $U_\ell$ for $\ell\mid N$) on the class-set ribbon lattice attached to the Eichler order of level $Nq$, for arbitrary abstract degeneracy data identified with the class-set data. It is the step used by the results producing quotient presentations of the class-set Hecke module and the descent-intertwining statements in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra
open CerednikDrinfeld

theorem CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      (if ℓ ∣ N then levelHeckeUSet Λ (meetOrder R n) ℓ else primeHeckeSet (meetOrder R n) ℓ))
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]

    {E V E'' V'' : Type} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]
    [Fintype E''] [Fintype V''] [DecidableEq V''] [DecidableEq E'']
    (D : DegeneracyData E V) (D'' : DegeneracyData E'' V'')
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ E)
    (hw : ∀ c, D.w (eE c) = (classSetDegeneracyData R n).w c)
    (eE'' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')) ≃ E'')
    (hw'' : ∀ c, D''.w (eE'' c) = (classSetDegeneracyData (meetOrder R s) n').w c)
    (e : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel (classSetDegeneracyData R n)))
    (he : ∀ (x : ↥(ribbonKernel D)) (c : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))),
      ((e x : ↥(ribbonKernel (classSetDegeneracyData R n))) :
          ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) c = (x : E → ℤ) (eE c))

    (μ₀ μ₁ : D''.FiniteHom D)
    (h₀ : ∀ c, μ₀.mapE (eE'' c) = eE (classSetForget _ _ c))
    (h₁ : ∀ c, μ₁.mapE (eE'' c) = eE (ClassSet.mk _ (c.out * s)))
    (z : ↥(ribbonKernel (classSetDegeneracyData R n))) :
    e (μ₀.pushforward (μ₁.pullback (e.symm z))) =
      heckeKernelMap (classSetHeckeData N q Λ R n) ⟨ℓ, Fact.out⟩ z := by sorry
