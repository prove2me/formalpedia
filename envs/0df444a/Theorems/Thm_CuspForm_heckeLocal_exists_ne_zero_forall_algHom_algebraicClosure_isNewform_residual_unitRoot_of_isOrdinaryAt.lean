-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_exists_ne_zero_forall_algHom_algebraicClosure_isNewform_residual_unitRoot_of_isOrdinaryAt
-- name    : CuspForm.heckeLocal.exists_ne_zero_forall_algHom_algebraicClosure_isNewform_residual_unitRoot_of_isOrdinaryAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/00bfe216-c59e-5c4c-82de-c69333ed2715
-- title:
--   Ordinary unit root at p ‖ N for every geometric point
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, let $p$ be an odd prime with $p\in\mathfrak m_{\mathcal O}$, let $\bar\rho$ be a two-dimensional residual Galois representation over $k$ (factoring through a finite level) which is absolutely irreducible, i.e. its base change to $\overline k$ is irreducible, let $S$ be a finite set of primes containing $p$, and let $N\neq 0$ have all its prime factors in $S$ and admit an integral structure in weight $2$. Let $\theta\colon \mathbb T^{S}(N)=\mathtt{heckeAlgebra}\ N\ 2\ S\to k$ be a ring homomorphism such that for every prime $\ell\nmid N$ with $\ell\notin S$, every valuation subring $P$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $P$ and every $\sigma$ acting as $x\mapsto x^{\ell}$ on the residue field of $P$ (so $\sigma$ lies in the decomposition subgroup), the characteristic polynomial of $\bar\rho(\sigma)$ is $X^{2}-\theta(T_\ell)X+\ell$. Assume $p\mid N$, $p^{2}\nmid N$, and that $\bar\rho$, viewed as an adic representation, is ordinary at $p$: for every $P$ lying over $p$ there is a line $L$ in the representation space, spanned by a basis vector, stable under the decomposition subgroup of $P$, with $\bar\rho(\sigma)v-v\in L$ for all $\sigma$ in the inertia subgroup and all $v$. Then there is $r\in k$, $r\neq0$, such that for every $\mathcal O$-algebra homomorphism $\chi$ from the local Hecke ring $\mathtt{heckeLocal}\ N\ S\ \mathcal O\ \theta$ to $\overline{\mathrm{Frac}\,\mathcal O}$ there exist a nonzero $M_g\mid N$, a weight-two cusp form $g$ on $\Gamma_0(M_g)$ which is a newform (a normalised eigenform whose eigensystem does not occur at any proper divisor of $M_g$), a ring homomorphism $\chi_g\colon\mathtt{heckeAlgebra}\ M_g\ 2\ \emptyset\to\mathbb C$ with $\chi_g(T_\ell)=a_\ell(g)$ for primes $\ell\nmid M_g$ and $\chi_g(U_q)=a_q(g)$ for primes $q\mid M_g$ (the $q$-expansion coefficients of $g$), and a ring homomorphism $\iota$ from the range of $\chi_g$ to $\overline{\mathrm{Frac}\,\mathcal O}$ with $\iota(\chi_g(T_\ell))=\chi(\pi(T_\ell))$ for all primes $\ell\nmid N$, $\ell\notin S$, and such that: if $p\mid M_g$ then $a_p(g)=a$ with $a=\pm1$ and $a$ is residually $r$, meaning there is a monic $R\in\mathcal O[X]$ with $R(a)=0$ and $\bar R=(X-r)^{\deg R}$ over $k$; while if $p\nmid M_g$ then $X^{2}-\iota(\chi_g(T_p))X+p$ factors as $(X-\alpha)(X-\beta)$ in $\overline{\mathrm{Frac}\,\mathcal O}$ with $\alpha$ residually $r$ and $\beta$ residually $0$, in the same sense.
--
--   This is the local analysis at a prime $p$ exactly dividing the level when $\bar\rho$ is ordinary at $p$: every geometric point of the local Hecke ring comes from a newform whose $p$-string contributes exactly one root congruent to a fixed non-zero $r$, the other root being residually zero. It feeds the newform-multiplicity computations at the corner, namely the statements that the residual root multiplicities sum to one and the identification of the newform multiplicity with the dimension of an intersection of Hecke eigenspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_exists_ne_zero_forall_algHom_algebraicClosure_isNewform_residual_unitRoot_of_isOrdinaryAt.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.exists_ne_zero_forall_algHom_algebraicClosure_isNewform_residual_unitRoot_of_isOrdinaryAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (hpN : p ∣ N) (hNp : ¬ p ^ 2 ∣ N)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p) :
    ∃ r : ResidueField 𝒪, r ≠ 0 ∧
      ∀ χ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪),
        ∃ (Mg : ℕ) (_ : NeZero Mg) (hMgN : Mg ∣ N)
          (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (_ : g.IsNewform)
          (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
          (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
            chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
          (_ : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
            chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
          (iota : chig.range →+* AlgebraicClosure (FractionRing 𝒪)),
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN))
              (Set.notMem_empty ℓ))) =
              χ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) ∧
        (p ∣ Mg → ∃ a : ℤ, (a = 1 ∨ a = -1) ∧ ModularFormClass.qCoeff g p = (a : ℂ) ∧
          (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪)) R = 0 ∧
          R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C r) ^ R.natDegree)) ∧
        (∀ hpMg : ¬ p ∣ Mg, ∃ α β : AlgebraicClosure (FractionRing 𝒪),
          (X ^ 2 - C (iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpMg
              (Set.notMem_empty p)))) * X + C ((p : ℕ) : AlgebraicClosure (FractionRing 𝒪)) :
              Polynomial (AlgebraicClosure (FractionRing 𝒪))) = (X - C α) * (X - C β) ∧
          (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval α R = 0 ∧
          R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C r) ^ R.natDegree) ∧
          (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval β R = 0 ∧
          R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)) := by sorry
