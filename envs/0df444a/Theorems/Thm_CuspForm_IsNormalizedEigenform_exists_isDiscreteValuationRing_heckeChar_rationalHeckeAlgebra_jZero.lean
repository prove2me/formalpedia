-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isDiscreteValuationRing_heckeChar_rationalHeckeAlgebra_jZero
-- name    : CuspForm.IsNormalizedEigenform.exists_isDiscreteValuationRing_heckeChar_rationalHeckeAlgebra_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/fdbe8a8a-053f-5a01-bfd3-239c59718a78
-- title:
--   Weight-two eigenform: eigencharacter into a characteristic-zero DVR
-- statement:
--   Fix $N\ge 1$ and a prime $p$. Assume the predicate [`ModularCurve.HeckeInputsAll N`](def/ModularCurve_HeckeInputsAll.html#L8), i.e. for every prime $\ell$ the condition `HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ` holds, and assume `HeckeOperatorsCommuteBar N`, i.e. the endomorphisms `heckeOperatorBar N ℓ` of $J_0(N)=$ [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115) (the group of degree-zero divisor classes of the modular function field of level $N$ base-changed to $\overline{\mathbb Q}$) commute pairwise; these make `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ act on $J_0(N)$ via `heckeModuleBar N`. Let $g$ be a cusp form of weight $2$ on $\Gamma_0(N)$ whose $q$-expansion coefficients satisfy $a_1=1$, multiplicativity at coprime indices, and the usual prime-power recursions in the two cases $\ell\nmid N$, $\ell\mid N$; let $k$ be a field of characteristic $p$ and $\varphi$ a ring homomorphism from the algebraic integers $\overline{\mathbb Z}=$ `integralClosure ℤ ℂ` to $k$. Then there exist a characteristic-zero discrete valuation ring $\mathcal O$ that is a $\mathbb Z_p$-algebra, ring homomorphisms $\theta\colon$ `HeckeAlg` $\to\mathcal O$ and $\Lambda$ from the $\mathbb Q_p$-subalgebra `rationalHeckeAlgebra p (JZero N)` of $\operatorname{End}_{\mathbb Q_p}$ of the rational Tate module to $\operatorname{Frac}\mathcal O$, and a local homomorphism $\psi\colon\mathcal O\to k$, such that $\Lambda$ sends the image of each $c\in\mathbb Z_p$ to the image of $c$ in $\operatorname{Frac}\mathcal O$, $\Lambda$ of `rationalHeckeRep p (JZero N) t` equals the image of $\theta(t)$ for every $t$, and for every prime $\ell\nmid N$ there is an algebraic integer $a$ with $a=a_\ell(g)$ in $\mathbb C$ and $\psi(\theta(X_\ell))=\varphi(a)$.
--
--   This packages the $p$-adic eigencharacter attached to a normalised weight-two eigenform: the Hecke eigenvalues are realised in a characteristic-zero discrete valuation ring over $\mathbb Z_p$, compatibly with the Hecke action on the rational Tate module of $J_0(N)$ and with the chosen reduction $\varphi$ of algebraic integers to $k$. It is used in the construction of the $p$-adic Galois representation attached to $g$, in [`CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_frobenius_quadratic`](thm.html#CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_frobenius_quadratic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_isDiscreteValuationRing_heckeChar_rationalHeckeAlgebra_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNormalizedEigenform.exists_isDiscreteValuationRing_heckeChar_rationalHeckeAlgebra_jZero
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    {k : Type} [Field k] [CharP k p] (φ : integralClosure ℤ ℂ →+* k) :
    letI := ModularCurve.heckeModuleBar N
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : CharZero O)
      (_ : Algebra ℤ_[p] O)
      (θ : ModularCurve.HeckeAlg →+* O)
      (Λ : ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) →+* FractionRing O)
      (ψ : O →+* k), IsLocalHom ψ ∧
      (∀ c : ℤ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) (c : ℚ_[p]))
          = algebraMap O (FractionRing O) (algebraMap ℤ_[p] O c)) ∧
      (∀ t : ModularCurve.HeckeAlg,
        Λ ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) t,
            ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) t⟩
          = algebraMap O (FractionRing O) (θ t)) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
          ψ (θ (ModularCurve.heckeGen ℓ)) = φ a) := by sorry
