-- Prove2me | Theorems.Thm_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
-- name    : AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/f989fbc1-0055-5530-b8f4-01f5dc890ccb
-- title:
--   Finiteness of s in a Haar pushforward s·ν
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $K_\infty$ denote the infinite adele ring of $K$, so that $L\otimes_K K_\infty$ is a commutative ring and $\mathrm{GL}_2(L\otimes_K K_\infty)$ its group of invertible $2\times 2$ matrices. Write $\sigma_{\mathrm{GL}}$ for the group endomorphism of $\mathrm{GL}_2(L\otimes_K K_\infty)$ obtained by applying entrywise the base change of $\sigma$ along $K_\infty$. Fix $\delta \in \mathrm{GL}_2(L\otimes_K K_\infty)$ and let $T$ be the subgroup $\{t : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1}=\delta\}$, equipped with the Borel $\sigma$-algebra of its subspace topology. Let $\tau$ be a measure on $T$ which is a Haar measure, and let $s \in [0,\infty]$. Give $M_2(L\otimes_K K_\infty)$ its Borel $\sigma$-algebra. The assertion is: for every measure $\nu$ on $M_2(L\otimes_K K_\infty)$, if the pushforward of $\tau$ along the map sending $t \in T$ to the underlying matrix of $t$ equals $s\cdot\nu$, then $s \ne \infty$.
--
--   In the archimedean part of the twisted-orbital mass computation, the Haar measure on a $\sigma$-twisted centraliser is compared with a Gram-normalised Lebesgue-type measure on matrix space through a scalar $s$; the statement rules out $s=\infty$, so that this normalising constant may be used as a finite factor. It is cited by the finiteness and residue-extraction results for integrals over the twisted centraliser that carry $s \ne \infty$ as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτa : τa.IsHaarMeasure)
    (s : ℝ≥0∞) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ ν : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa =
        s • ν →
      s ≠ ⊤ := by sorry
