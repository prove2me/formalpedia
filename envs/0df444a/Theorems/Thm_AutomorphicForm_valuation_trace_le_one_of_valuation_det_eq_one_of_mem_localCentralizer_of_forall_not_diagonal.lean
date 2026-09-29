-- Prove2me | Theorems.Thm_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
-- name    : AutomorphicForm.valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/46915d37-1b43-5e43-b4aa-39c43c124899
-- title:
--   Unit determinant forces integral trace in an elliptic torus
-- statement:
--   Let $K$ be a number field and let $v$ be a nonzero prime ideal of its ring of integers $\mathcal{O}_K$, with $K_v$ the $v$-adic completion of $K$, carrying its canonical multiplicative valuation `Valued.v`. Let $\gamma_0 \in \mathrm{GL}_2(K_v)$ be regular semisimple in the sense of the project's predicate [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), namely that $\operatorname{tr}(\gamma_0)^2 - 4\det(\gamma_0)$ is a unit of $K_v$, and assume that $\gamma_0$ is not diagonalisable over $K_v$ in the strong form: for every $g \in \mathrm{GL}_2(K_v)$ the matrix of $g^{-1}\gamma_0 g$ does not have both off-diagonal entries $(0,1)$ and $(1,0)$ equal to zero. Let $m \in \mathrm{GL}_2(K_v)$ lie in the centralizer of the singleton $\{\gamma_0\}$, i.e. $m$ commutes with $\gamma_0$, and suppose the determinant of the matrix of $m$ has valuation $1$ (it is a unit of the valuation ring). Then the trace of the matrix of $m$ also has valuation at most $1$, i.e. it lies in the valuation ring of $K_v$.
--
--   Under the stated hypotheses the centralizer of $\gamma_0$ is the multiplicative group of the quadratic field extension $K_v[\gamma_0]$, and the assertion is the standard fact that an element of that extension whose norm is a unit is itself integral, hence has integral trace. It supplies the integrality input for the set of "torus units" used in the local volume computations for elliptic orbital integrals, and is cited in the comparison of Weil constants with measures of torus unit groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (m : GL (Fin 2) (v.adicCompletion K)) (hm : m ∈ AutomorphicForm.localCentralizer K v γ₀)
    (hdet : Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1) :
    Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1 := by sorry
