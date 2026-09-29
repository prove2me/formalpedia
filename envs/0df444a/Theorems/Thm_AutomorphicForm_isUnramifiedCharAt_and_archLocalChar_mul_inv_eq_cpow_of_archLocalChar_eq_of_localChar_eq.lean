-- Prove2me | Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_and_archLocalChar_mul_inv_eq_cpow_of_archLocalChar_eq_of_localChar_eq
-- name    : AutomorphicForm.isUnramifiedCharAt_and_archLocalChar_mul_inv_eq_cpow_of_archLocalChar_eq_of_localChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/bcad28ef-291c-5f2e-9e53-14d1c7b7eea5
-- title:
--   Quotient of two idele class characters with equal weights
-- statement:
--   Let $K$ be a number field, $SK$ a finite set of height-one primes of $\mathcal O_K$, and let $\mu,\mu' \colon (\mathbb A_K)^\times \to \mathbb C^\times$ be group homomorphisms such that $\|\mu(x)\| = \|\mu'(x)\| = 1$ for all ideles $x$, such that $\mu$ and $\mu'$ are trivial on the principal ideles $\mathrm{image}$ of $K^\times$ under $K \to \mathbb A_K$, and such that both are continuous as $\mathbb C$-valued functions. Let $\tau,\tau' \colon \mathrm{InfinitePlace}\,K \to \mathbb R$, and assume: for every infinite place $v$ and every $x \in (K_v)^\times$ whose image under the embedding $K_v \to \mathbb C$ is a positive real number, the value of $\mu$ (resp. $\mu'$) at the idele with component $x$ at $v$ and $1$ elsewhere equals $N(x)^{\tau_v i}$ (resp. $N(x)^{\tau'_v i}$), where $N$ denotes the idele norm, defined as the modulus of the scaling action on Haar measure. Let $m \colon \mathrm{InfinitePlace}\,K \to \mathbb Z$ and assume that for every infinite place $v$ and every $x \in (K_v)^\times$ of absolute value $1$, both $\mu$ and $\mu'$ take the value $x^{m_v}$ (image of $x$ in $\mathbb C$) at that same idele. Assume further that for every prime $v \notin SK$ both $\mu$ and $\mu'$ are trivial on the image of the local units $\mathcal O_v^\times$ (those $t \in (K_v)^\times$ with $t$ and $t^{-1}$ in the valuation ring), embedded at $v$ with $1$ at all other places, and that there are homomorphisms $\rho_v \colon (K_v)^\times \to \mathbb C^\times$ with which both local restrictions of $\mu$ and $\mu'$ agree on $\mathcal O_v^\times$ for each $v \in SK$. Then $\chi = \mu \mu'^{-1}$ again has all its values of absolute value $1$, is trivial on principal ideles, is continuous, is trivial on $\mathcal O_v^\times$ at every height-one prime $v$, and satisfies, for every infinite place $v$ and every $x \in (K_v)^\times$ without restriction, $\chi(x) = N(x)^{(\tau_v - \tau'_v) i}$ at the idele with component $x$ at $v$ and $1$ elsewhere.
--
--   This is the elementary divide-out step for Hecke characters of a number field: two continuous unitary idele class characters with the same archimedean weights $m_v$ and the same restriction to the local units at the places of a fixed finite set have a quotient of level one whose remaining invariant is the difference of the archimedean parameter vectors. It is used in the counting of archimedean parameters of automorphic characters, in [`AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles`](thm.html#AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnramifiedCharAt_and_archLocalChar_mul_inv_eq_cpow_of_archLocalChar_eq_of_localChar_eq.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isUnramifiedCharAt_and_archLocalChar_mul_inv_eq_cpow_of_archLocalChar_eq_of_localChar_eq
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (μ μ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 K) K μ) (hμ' : IsUnitaryChar (𝓞 K) K μ')
    (hμic : IsIdeleClassChar (𝓞 K) K μ) (hμic' : IsIdeleClassChar (𝓞 K) K μ')
    (hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hμc' : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ))
    (τ τ' : InfinitePlace K → ℝ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τ v : ℝ) : ℂ) * Complex.I))
    (hτ' : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar μ' v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τ' v : ℝ) : ℂ) * Complex.I))
    (m : InfinitePlace K → ℤ)
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (hm' : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar μ' v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt μ' v)
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hS : ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        NumberField.TateGlobal.localChar μ v u = ρ v u ∧ NumberField.TateGlobal.localChar μ' v u = ρ v u) :
    IsUnitaryChar (𝓞 K) K (μ * μ'⁻¹) ∧ IsIdeleClassChar (𝓞 K) K (μ * μ'⁻¹) ∧
    (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * μ'⁻¹) z : ℂˣ) : ℂ)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt (μ * μ'⁻¹) v) ∧
    ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ((NumberField.TateGlobal.archLocalChar (μ * μ'⁻¹) v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τ v - τ' v : ℝ) : ℂ) * Complex.I) := by sorry
