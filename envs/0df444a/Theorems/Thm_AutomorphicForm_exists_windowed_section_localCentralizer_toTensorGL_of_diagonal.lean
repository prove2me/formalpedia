-- Prove2me | Theorems.Thm_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
-- name    : AutomorphicForm.exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/5244c80c-f848-5f8c-a14d-a5187702eb4b
-- title:
--   Windowed section for the diagonal torus acting on GL₂(L⊗_K Kᵥ)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal O_K$, and write $K_v$ for the $v$-adic completion of $K$ and $\mathcal O_v$ for its valuation ring. Let $a,b\in K_v$ with $a\neq b$ and let $\gamma\in\mathrm{GL}_2(K_v)$ have matrix $\begin{pmatrix}a&0\\0&b\end{pmatrix}$. Let $A=\mathrm{Subgroup.centralizer}\,\{\gamma\}$, carrying the Borel $\sigma$-algebra of its subspace topology, and let $\tau$ be a Haar measure on $A$ assigning mass $1$ to the set of $s\in A$ whose image in $\mathrm{GL}_2(K_v)$ lies in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), i.e. such that the matrices of $s$ and of $s^{-1}$ both lie in `integralMatrixSet` of $\mathcal O_v$. Then there is a function $\beta:\mathrm{GL}_2(L\otimes_K K_v)\to\mathbb R$, measurable for the Borel $\sigma$-algebra on $\mathrm{GL}_2(L\otimes_K K_v)$, with $0\le\beta\le 1$ pointwise, such that for every $u\in\mathrm{GL}_2(L\otimes_K K_v)$ whose $(0,1)$ and $(1,0)$ entries vanish one has $\int_A \beta\bigl(\iota(s)\,u\bigr)\,d\tau(s)=1$, where $\iota$ is the homomorphism [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) induced by $x\mapsto 1\otimes x$, and moreover, for such $u$, if $\beta(u)\neq0$ then both $\|N(u_{00})\|$ and $\|N(u_{11})\|$ lie in the interval $\bigl(\mathrm{absNorm}(v)^{-[L:K]},\,1\bigr]$, $N$ denoting the algebra norm over $K_v$ of $L\otimes_K K_v$.
--
--   This is the local normalisation step used in the analysis of twisted orbital integrals at a regular split element $\gamma=\mathrm{diag}(a,b)$: it produces a $[0,1]$-valued Borel cut-off on $\mathrm{GL}_2(L\otimes_K K_v)$ which has total mass one along each orbit of the diagonal torus $A$ and whose support confines the norms of the diagonal entries to a window of multiplicative width $q^{-[L:K]}$. It is cited in the proof of the uniform bound [`AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul`](thm.html#AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_windowed_section_localCentralizer_toTensorGL_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_windowed_section_localCentralizer_toTensorGL_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (hτ1 : τ {s : AutomorphicForm.localCentralizer K v γ |
      (s : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1) :
    ∃ β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β ∧
      (∀ x, 0 ≤ β x) ∧ (∀ x, β x ≤ 1) ∧
      (∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ s : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (s : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1) ∧
      (∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        β u ≠ 0 →
          (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L <
              ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖ ∧
            ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0)‖ ≤ 1) ∧
          (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ Module.finrank K L <
              ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ∧
            ‖Algebra.norm (v.adicCompletion K) ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ≤ 1)) := by sorry
