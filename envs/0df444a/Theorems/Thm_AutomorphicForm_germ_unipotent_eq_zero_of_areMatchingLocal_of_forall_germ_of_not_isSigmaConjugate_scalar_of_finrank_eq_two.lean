-- Prove2me | Theorems.Thm_AutomorphicForm_germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0efa3da0-9949-5a0a-9aa2-e671d04823b8
-- title:
--   Vanishing of the unipotent germ at a non-σ-conjugate scalar
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism of $L$ lies in the subgroup of integral powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal{O}_K$, let $c$ be a unit of the completion $K_v$, and let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ be such that the scalar matrix $c\cdot 1$ is a norm of $\delta$ in the sense of [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217), i.e. $\delta$ admits a $y$ with $y^{-1}\,(\text{the }\sigma\text{-norm string of }\delta)\,y$ equal to the image of $c\cdot 1$ in $\mathrm{GL}_2(L\otimes_K K_v)$, while for no unit $z$ of $L\otimes_K K_v$ is $\delta$ $\sigma$-conjugate to $z\cdot 1$ (there is no $x$ with $z\cdot 1 = x^{-1}\delta\,\sigma(x)$). Let $\varphi_v$ be a complex function on $\mathrm{GL}_2(L\otimes_K K_v)$ and $f_v$ a local test function on $\mathrm{GL}_2(K_v)$, that is, locally constant with compact support, and assume $\varphi_v$ and $f_v$ satisfy [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386), the matching relation `AreMatchingOn` for $\sigma$ taken with respect to the semilocal Haar measure on $\mathrm{GL}_2(L\otimes_K K_v)$ and the Haar measure on $\mathrm{GL}_2(K_v)$. Let $\nu$ be a complex-valued functional on functions $\mathrm{GL}_2(K_v)\to\mathbb{C}$ subject to the following germ-expansion hypothesis: for every regular semisimple $\gamma_0 \in \mathrm{GL}_2(K_v)$, meaning $\operatorname{tr}(\gamma_0)^2 - 4\det(\gamma_0)$ is a unit, and every Borel measure $\nu_T$ on $\mathrm{GL}_2(K_v)$, there are $A \in \mathbb{C}$ and $B : \mathrm{GL}_2(K_v) \to \mathbb{C}$ such that (i) for every local test function $f$ there is a neighbourhood $W$ of $c\cdot 1$ such that for every regular semisimple $\gamma \in W$ centralising $\gamma_0$, every Haar measure $\tau$ on the centraliser of $\gamma$ pushing forward along the inclusion to $\nu_T$, and every $I$ which is an orbital integral of $f$ at $\gamma$ with respect to $\tau$, one has $I = A\,f(c\cdot 1) + B(\gamma)\,\nu(f)$; (ii) if $\gamma_0$ has vanishing $(0,1)$ and $(1,0)$ entries and the pullback of $\nu_T$ to the centraliser of $\gamma_0$ is Haar, then $A = 0$ and on some neighbourhood $W$ of $c\cdot 1$ one has $B(\gamma) \neq 0$ for all regular semisimple $\gamma \in W$ centralising $\gamma_0$; and (iii) if no conjugate $g^{-1}\gamma_0 g$ has both off-diagonal entries zero and the pullback of $\nu_T$ to the centraliser of $\gamma_0$ is Haar, then $A \neq 0$. The conclusion is $\nu(f_v) = 0$.
--
--   This is the split-torus vanishing step in the local comparison of twisted and ordinary orbital integrals for $\mathrm{GL}_2$ over a quadratic extension: the Shalika germ expansion on a split torus forces the unipotent germ coefficient functional to annihilate the local test function matched with $\varphi_v$ at a scalar which is a norm of a $\delta$ that is not $\sigma$-conjugate to a scalar. It feeds the identification of the twisted orbital integral at such a $\delta$ with the negative of the orbital integral at the scalar $c\cdot 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φv fv)
    (ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ)
    (hν : ∀ (γ₀ : GL (Fin 2) (v.adicCompletion K)), AutomorphicForm.IsRegularSemisimple γ₀ →
        ∀ (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)),
        ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),

          (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
              ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
                @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
                @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                    Subtype.val τ = νT →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                  I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) ∧

          (((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
              (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A = 0 ∧
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ → B γ ≠ 0) ∧

          ((∀ g : GL (Fin 2) (v.adicCompletion K),
              ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
                 ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A ≠ 0)) :
    ν fv = 0 := by sorry
