-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
-- name    : AutomorphicForm.exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/25bb3aa8-b76f-55b8-bbed-526ed625a09e
-- title:
--   Bounded Borel section for the diagonal torus in GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and write $K_v$ for the $v$-adic completion of $K$. Let $a,b \in K_v$ with $a \neq b$, and let $\gamma \in \mathrm{GL}_2(K_v)$ be an element whose underlying matrix is $\mathrm{diag}(a,b)$. Let $T$ denote the centraliser of the singleton $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, regarded as a measurable space via the Borel $\sigma$-algebra of its topology, and let $\tau$ be a Haar measure on $T$. The assertion is that there exists a function $\beta \colon \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{R}$ which is measurable for the Borel $\sigma$-algebra on $\mathrm{GL}_2(L \otimes_K K_v)$, satisfies $\beta \geq 0$ and $\beta \leq C$ for some real constant $C$, and is such that for every $u \in \mathrm{GL}_2(L \otimes_K K_v)$ whose matrix entries in positions $(0,1)$ and $(1,0)$ both vanish one has $$\int_T \beta\bigl(\iota(t)\,u\bigr)\,\mathrm{d}\tau(t) = 1,$$ where $\iota \colon \mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ is the group homomorphism induced entrywise by $x \mapsto 1 \otimes x$.
--
--   The function $\beta$ is a bounded Borel section function for the action of the diagonal torus $T \cong K_v^\times \times K_v^\times$ by left translation on the diagonal elements of $\mathrm{GL}_2(L \otimes_K K_v)$, normalised so that its integral over each orbit is $1$; it serves in place of a quotient measure on $T \backslash (L \otimes_K K_v)^\times{}^2$ when twisted orbital integrals at diagonal elements are unfolded in coordinates. It is used in the derivation of the growth estimate for twisted orbital integrals of indicator functions of semi-local integral sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ) :
    ∃ β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β ∧
      (∀ x, 0 ≤ β x) ∧ (∃ C : ℝ, ∀ x, β x ≤ C) ∧
      ∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ t : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (t : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1 := by sorry
