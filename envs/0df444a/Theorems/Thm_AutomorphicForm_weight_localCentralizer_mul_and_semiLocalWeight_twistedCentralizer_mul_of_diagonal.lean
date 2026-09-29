-- Prove2me | Theorems.Thm_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
-- name    : AutomorphicForm.weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/e746ce41-cacb-5f92-96a5-81671e7c6320
-- title:
--   Local and semi-local weights are invariant under (twisted) centralisers of diagonal elements
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $v$ be a nonzero prime of $\mathcal{O}_K$, with $K_v$ the $v$-adic completion. The theorem asserts a conjunction of two invariance statements. First: for every $\gamma_v \in \mathrm{GL}_2(K_v)$ whose $(1,0)$ and $(0,1)$ entries vanish, i.e. which is diagonal, and which satisfies the regular semisimplicity condition that $\operatorname{tr}(\gamma_v)^2 - 4\det(\gamma_v)$ is a unit, for every $t$ in the centraliser of $\{\gamma_v\}$ in $\mathrm{GL}_2(K_v)$ and every $x \in \mathrm{GL}_2(K_v)$, one has $\mathrm{weight}(t x) = \mathrm{weight}(x)$, where $\mathrm{weight}(y) = 2\log\bigl(\max(\|y_{00}\|,\|y_{01}\|)\cdot\max(\|y_{10}\|,\|y_{11}\|)/\|\det y\|\bigr)$. Second: for every $\delta_v \in \mathrm{GL}_2(L \otimes_K K_v)$ which is diagonal in the same sense, and such that the norm string $\prod_{i=0}^{[L:K]-1} \sigma^i(\delta_v)$ — the ordered product of the iterates of $\delta_v$ under the entrywise action of $\sigma$ on $L \otimes_K K_v$ — has $\operatorname{tr}^2 - 4\det$ a unit, for every $t$ in the $\sigma$-twisted centraliser $\{t : t\,\delta_v\,\sigma(t)^{-1} = \delta_v\}$ and every $x \in \mathrm{GL}_2(L \otimes_K K_v)$, the semi-local weight is unchanged: $W_v(t x) = W_v(x)$, where $W_v(y)$ is the (finite) sum over the primes $w$ of $\mathcal{O}_L$ lying under $v$ of $\mathrm{weight}$ of the $w$-component of $y$, taken via the base-change identification $L \otimes_K K_v \cong \prod_w L_w$.
--
--   This is the invariance of the local height weight under left multiplication by elements of the centraliser, respectively the $\sigma$-twisted centraliser, of a diagonal regular element — the property that makes the weight factor pass through to weighted orbital integrals in the base-change comparison for $\mathrm{GL}_2$. It supplies the weight-invariance hypotheses of the weighted Euler factorisation statements and of the comparison of weighted and twisted weighted orbital integrals at diagonal elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ γv : GL (Fin 2) (v.adicCompletion K),
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple γv →
      ∀ t : AutomorphicForm.localCentralizer K v γv, ∀ x : GL (Fin 2) (v.adicCompletion K),
        AutomorphicForm.LocalWeight.weight ((t : GL (Fin 2) (v.adicCompletion K)) * x) =
          AutomorphicForm.LocalWeight.weight x) ∧
    (∀ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δv) →
      ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δv,
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.semiLocalWeight K L v ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x) =
            AutomorphicForm.semiLocalWeight K L v x) := by sorry
