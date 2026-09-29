-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
-- name    : AlgebraicCurve.Pic0.conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/deffc174-590e-5704-aa6b-fd458650442c
-- title:
--   Equivariance of the conorm on Pic⁰ under compatible semilinear automorphisms
-- statement:
--   Let $K,F,K',F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra and $F'$ an $F$-algebra. A place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring; divisors are finitely supported integer-valued functions on places, the degree-zero ones form the kernel of the degree homomorphism, and $\mathrm{Pic}^0$ is the quotient of the degree-zero divisors by the subgroup of principal divisors lying in it. Let $\iota \colon \mathrm{Pic}^0(K,F) \to \mathrm{Pic}^0(K',F')$ be an additive homomorphism subject to two hypotheses: (`hpin`) whenever $D$ is a degree-zero divisor of $F/K$ and $D'$ one of $F'/K'$ such that $D'(v') = D(v)$ for all places $v',v$ with the preimage of the valuation subring of $v'$ along $\mathrm{algebraMap}\ F\ F'$ equal to that of $v$, and $D'(v') = 0$ for every $v'$ whose preimage is the valuation subring of no place of $F/K$, then $\iota[D] = [D']$; and (`hex`) every degree-zero $D$ admits such a $D'$. Let $\sigma$ be an element of `SemilinearAut K F`, i.e. a pair consisting of a ring automorphism of $F$ and one of $K$ intertwined by $\mathrm{algebraMap}\ K\ F$, and likewise $\sigma'$ in `SemilinearAut K' F'`, and assume they are compatible along $F \to F'$: $\sigma' \cdot \mathrm{algebraMap}\ F\ F'(f) = \mathrm{algebraMap}\ F\ F'(\sigma \cdot f)$ for all $f \in F$. Then $\iota(\sigma \cdot x) = \sigma' \cdot \iota(x)$ for every $x \in \mathrm{Pic}^0(K,F)$.
--
--   This is the functoriality of the conorm map of degree-zero divisor class groups in a semilinear automorphism: the conorm along $F \to F'$, characterised here only by the pinning property `hpin` together with the existence property `hex`, intertwines the actions of compatible semilinear automorphisms of $F/K$ and $F'/K'$. It is used in the construction of Čerednik–Drinfeld Shimura curve models, where $\mathrm{Pic}^0$ of a curve is compared equivariantly with $\mathrm{Pic}^0$ after a constant field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible.lean

import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra F F']
    (ι : Pic0 K F →+ Pic0 K' F')
    (hpin : ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) →
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (hex : ∀ D : Divisor.degZero (K := K) (F := F), ∃ D' : Divisor.degZero (K := K') (F := F'),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0))
    (σ : SemilinearAut K F) (σ' : SemilinearAut K' F')
    (hcompat : ∀ f : F, σ' • algebraMap F F' f = algebraMap F F' (σ • f)) :
    ∀ x : Pic0 K F, ι (σ • x) = σ' • ι x := by sorry
