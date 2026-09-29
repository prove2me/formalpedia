-- Prove2me | Theorems.Thm_AutomorphicForm_areMatchingArch_central_transfer_of_scalar
-- name    : AutomorphicForm.areMatchingArch_central_transfer_of_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/ff8b1338-5844-5063-b900-72edc1bdba33
-- title:
--   Archimedean central transfer for matching archimedean test factors
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, of prime degree $[L:K]$, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ and $f_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ be archimedean test factors, i.e. each is compactly supported and factors through the matrix entries transported to the mixed space ($\varphi_a(g) = \Phi(\mathrm{archEntries}\,g)$ for some $\Phi$ that is $C^\infty$ over $\mathbb{R}$, and likewise for $f_a$), and assume the pair $(\varphi_a \circ \mathrm{archIdentGL}, f_a)$ satisfies the matching predicate `AreMatchingOn` relative to $\sigma$ and the Haar measures `archHaarL`, `archHaarK` on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and $\mathrm{GL}_2(K_\infty)$. The conclusion is the matching identity at central elements: for every $\gamma \in \mathrm{GL}_2(K_\infty)$ which is a scalar matrix $\mathrm{scalar}(c)$ with $c \in (K_\infty)^\times$, for all $\delta, y \in \mathrm{GL}_2(L \otimes_K K_\infty)$ with $\gamma$ (pushed forward along $A \to L \otimes_K A$) equal to $y^{-1}\,(\mathrm{normString}\,\sigma\,\delta)\,y$, for all Haar measures $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_\infty)$ and $\tau'$ on the $\sigma$-twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$ (both with their Borel structures) that are coupled, meaning that the image of $\tau'$ under $t \mapsto y^{-1} t y$ coincides with the image of $\tau$ under the map $\mathrm{GL}_2(K_\infty) \to \mathrm{GL}_2(L \otimes_K K_\infty)$, and for all $I, I' \in \mathbb{C}$ such that $I'$ is a value of the $\sigma$-twisted orbital integral $\int \varphi_a(\mathrm{archIdentGL}(x^{-1}\delta\,\sigma(x)))\,w(x)$ at $\delta$ against `archHaarL` with a twisted section function $w$ for $\tau'$, and $I$ is a value of the orbital integral $\int f_a(x^{-1}\gamma x)\,w(x)$ at $\gamma$ against `archHaarK` with a section function for $\tau$, one has $I' = I$.
--
--   This is the central (scalar) case of the archimedean matching identity for twisted orbital integrals in the base-change comparison for $\mathrm{GL}_2$ along a cyclic extension of prime degree: matching archimedean test factors automatically transfer at the scalars of $\mathrm{GL}_2(K_\infty)$, not merely at regular semisimple elements. It feeds the global comparison of twisted and ordinary orbital integrals at central elements used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_areMatchingArch_central_transfer_of_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.areMatchingArch_central_transfer_of_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hm : AutomorphicForm.AreMatchingArch K L σ φa fa) :
    (∀ γ : GL (Fin 2) (InfiniteAdeleRing K),
      (∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
        (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ →
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = I) := by sorry
