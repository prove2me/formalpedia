-- Prove2me | Theorems.Thm_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
-- name    : AutomorphicForm.eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/779cad41-7d02-527e-a439-15c46e6cc42b
-- title:
--   Archimedean twisted weighted orbital integrals: lift independence and scaling
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Write $K_\infty$ for the infinite adele ring of $K$. Let $\gamma \in GL_2(K_\infty)$ be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit, and assume its $(0,1)$ and $(1,0)$ entries vanish. Let $\nu'$ be a Haar measure on $GL_2(L \otimes_K K_\infty)$ for the Borel $\sigma$-algebra, and $wt : GL_2(L \otimes_K K_\infty) \to \mathbb{R}$ a continuous weight satisfying $wt(tx) = wt(x)$ whenever the $(0,1)$ and $(1,0)$ entries of $t$ vanish. Let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $GL_2(K_\infty)$ and let $c > 0$. Let $\delta_1, \delta_2 \in GL_2(L \otimes_K K_\infty)$ both have norm string $\delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$, $n = [L:K]$ (the product over $i \in \{0,\dots,n-1\}$ of the $i$-th iterate of the map induced by $\sigma$ on $GL_2(L \otimes_K K_\infty)$), equal to the image of $\gamma$ under the map induced by $a \mapsto 1 \otimes a$. Let $\tau'_j$ be Haar measures on the twisted centralisers $\{t : t\delta_j\sigma(t)^{-1} = \delta_j\}$, coupled to $\tau$ and to $c \cdot \tau$ respectively through the conjugator $1$, meaning that the pushforward of $\tau'_1$ along $t \mapsto t$ equals the pushforward of $\tau$ along $t \mapsto 1 \otimes t$, and likewise for $\tau'_2$ with $\tau$ replaced by $(\mathrm{ofReal}\,c) \cdot \tau$. Let $\varphi_a : GL_2(L_\infty) \to \mathbb{C}$ be an archimedean test factor, i.e. $\varphi_a(g) = \Phi$ evaluated at the matrix of archimedean entries of $g$ for some smooth $\Phi$ on matrices over the mixed space of $L$, with $\varphi_a$ compactly supported. Finally let $J'_1, J'_2 \in \mathbb{C}$ be values of the twisted weighted orbital integral relation for $(\delta_j, \tau'_j)$: there is a section function $s \ge 0$, measurable with compact support, with $\int s(tx)\,d\tau'_j = 1$ for every $x$ at which the integrand is nonzero, and $J'_j = \int \varphi(x^{-1}\delta_j\sigma(x))\, wt(x)\, s(x)\, d\nu'$, where $\varphi$ is $\varphi_a$ read through the identification $L \otimes_K K_\infty \cong L_\infty$ on $GL_2$. Then $J'_2 = c^{-1} J'_1$.
--
--   This is the archimedean instance of the comparison of twisted weighted orbital integrals at a split regular norm: the value is independent of the chosen lift $\delta$ of $\gamma$ along the norm map, and depends on the measure on the twisted centraliser only through the coupling constant, scaling inversely with it. It feeds the archimedean side of the twisted weighted class integral identities and of the window estimates used in the base-change comparison for $GL(2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField TensorProduct
open scoped TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.eq_inv_mul_of_isTwistedWeightedOrbitalIntegralOn_of_normString_eq_toTensorGL_diagonal_of_coupled_one_smul_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (ν' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν')
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 → (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 →
        wt (t * x) = wt x)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (δ₁ δ₂ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ₁ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ₁ =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (hδ₂ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ₂ =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (τ'₁ : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₁)) (hτ'₁ : τ'₁.IsHaarMeasure)
    (hc₁ : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ₁ 1 τ τ'₁)
    (τ'₂ : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ₂)) (hτ'₂ : τ'₂.IsHaarMeasure)
    (hc₂ : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ₂ 1 (ENNReal.ofReal c • τ) τ'₂)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (J'₁ J'₂ : ℂ)
    (hJ'₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ₁ τ'₁
      (φa ∘ AutomorphicForm.archIdentGL K L) J'₁)
    (hJ'₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν' wt δ₂ τ'₂
      (φa ∘ AutomorphicForm.archIdentGL K L) J'₂) :
    J'₂ = (c : ℂ)⁻¹ * J'₁ := by sorry
