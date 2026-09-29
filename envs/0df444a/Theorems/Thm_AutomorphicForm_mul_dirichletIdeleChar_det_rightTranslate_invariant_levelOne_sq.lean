-- Prove2me | Theorems.Thm_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
-- name    : AutomorphicForm.mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/327d39ef-b648-54d4-9ba0-852950708f51
-- title:
--   Level-M² invariance of a twisted translate of φ
-- statement:
--   Fix a positive integer $M$ and a Dirichlet character $\chi$ modulo $M$ with values in $\mathbb{C}$, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$. Write $\iota$ for the monoid homomorphism [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) sending a finite-adelic matrix to the adelic matrix with the same finite components and the identity at the infinite places, and $\mathrm{diag}(a,1)$ for [`NumberField.AdelicLevel.diagOne`](def/NumberField_AdelicLevel.html#L624). Two hypotheses on $\varphi$ are assumed. First, $\varphi(x\,\iota(k))=\varphi(x)$ for all adelic $x$ and all $k\in\mathrm{GL}_2$ of the finite adeles such that every entry of $k-1$ and every entry of $k^{-1}-1$ lies in the ball `idealBall` of the ideal $(M)$, i.e. has valuation at most the bound attached to $(M)$ at each finite place. Secondly, for every unit $u$ of the finite adele ring with $u$ and $u^{-1}$ integral at all finite places, $\varphi(x\,\iota(\mathrm{diag}(u,1)))=\chi\bigl(\mathrm{unitResidue}_M(\det \iota(\mathrm{diag}(u,1)))\bigr)\varphi(x)$, where $\mathrm{unitResidue}_M$ is the homomorphism from adelic units to $\mathbb{Z}/M$ assembled from the $p$-adic residues modulo $p^{v_p(M)}$ for $p\mid M$. Let $s=\iota(\mathrm{diag}(M,1)^{-1})$, $M$ being inverted in $\mathbb{Q}$ and mapped into the finite adeles. Then for every adelic $x$ and every $k$ in the subgroup `finiteLevelOne` of level $(M)^2$ — both $k$ and $k^{-1}$ satisfying `IsLevelOneMatrix` for $(M)^2$, namely the conditions of `IsLevelZeroMatrix` together with the lower-right entry minus $1$ lying in `idealBall` of $(M)^2$ — one has $$\varphi(x\,\iota(k)\,s)\,\eta(\det(x\,\iota(k)))=\varphi(x\,s)\,\eta(\det x),$$ where $\eta=$ [`DirichletCharacter.dirichletIdeleChar`](def/DirichletCharacter_DirichletIdeleChar.html#L125) $\chi$ is the homomorphism from adelic units to $\mathbb{C}^\times$ inverse to $\chi\circ\mathrm{unitResidue}_M$.
--
--   This is the step that moves a vector invariant under the principal congruence level $M$, with the prescribed determinant behaviour, into a vector invariant under a $K_1$-type level of level $M^2$: conjugating by $\mathrm{diag}(M,1)$ and twisting by the idele class character attached to $\chi$, the function $x\mapsto\varphi(xs)\eta(\det x)$ becomes right invariant under that level group. It is used in the proof that a cuspidal constituent with prescribed right-translation behaviour spans a finite-dimensional space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq.lean

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (φ : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ)
    (hK : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2)
          (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      (∀ i j, (((k⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) = φ x)
    (hT : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (u : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ),
      (u : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      ((u⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)) =
        χ (RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)))) *
          φ x)
    (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (hk : k ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
      (Ideal.span {(M : NumberField.RingOfIntegers ℚ)} ^ 2)) :
    φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k *
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det
          (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k)) : ℂˣ) : ℂ) =
      φ (x * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := by sorry
