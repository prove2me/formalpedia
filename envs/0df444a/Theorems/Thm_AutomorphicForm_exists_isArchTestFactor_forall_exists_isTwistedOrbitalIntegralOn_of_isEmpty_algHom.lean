-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- name    : AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/ef158d9c-c232-5368-8378-450f85fe412a
-- title:
--   Archimedean transfer for quadratic base change of GL₂
-- statement:
--   Let $K \subset L$ be number fields with $[L:K]=2$, let $\sigma$ be a non-trivial $K$-automorphism of $L$, and assume there is no $K$-algebra map $L \to K_\infty$ into the infinite adeles of $K$. Let $\mathrm{tys}_L$ be an archimedean type family for $L$ (a number $\mathrm{card}\,w$ of types at each infinite place $w$, together with that many archimedean representation data at $w$), and let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be an archimedean test factor, i.e. $\varphi_a$ has compact support and is $\Phi \circ \mathrm{archEntries}$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $L$, and be bi-finite for $\mathrm{tys}_L$, i.e. $g \mapsto \varphi_a(g^{-1})$ lies in `archFactorCutSubmodule` and $\varphi_a$ in `archFactorDualCutSubmodule` for $\mathrm{tys}_L$. Then there are an archimedean type family $\mathrm{tys}_K$ for $K$ and a function $f_a$ on $\mathrm{GL}_2(K_\infty)$ which is again an archimedean test factor and bi-finite for $\mathrm{tys}_K$, such that: (1) for every $\delta \in \mathrm{GL}_2(L \otimes_K K_\infty)$ whose norm string $\prod_{i<2}\sigma^i(\delta)$ is regular semisimple (the discriminant $\mathrm{tr}^2-4\det$ is a unit), every regular semisimple $\gamma \in \mathrm{GL}_2(K_\infty)$, every $y$ with $\gamma = y^{-1}\,(\prod_i \sigma^i \delta)\,y$ in $\mathrm{GL}_2(L\otimes_K K_\infty)$, and every pair of Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser of $\delta$ that are coupled (the image of $\tau'$ under $t \mapsto y^{-1}ty$ equals the image of $\tau$ under the tensor inclusion), one and the same $I \in \mathbb{C}$ is a value of the $\sigma$-twisted orbital integral $\int \varphi_a(\mathrm{archIdentGL}(x^{-1}\delta\,\sigma(x)))\,w(x)$ at $\delta$ against `archHaarL`, for a twisted section weight $w$ adapted to $\tau'$, and a value of the orbital integral $\int f_a(x^{-1}\gamma x)\,w(x)$ at $\gamma$ against `archHaarK`, for a section weight adapted to $\tau$; and (2) for every regular semisimple $\gamma \in \mathrm{GL}_2(K_\infty)$ which is not a norm, i.e. no $\delta$ and $y$ satisfy the above conjugacy relation, and every Haar measure $\tau$ on its centraliser, $0$ is such a realised value of the orbital integral of $f_a$ at $\gamma$.
--
--   This is the archimedean half of the transfer (Shintani matching) of orbital integrals for quadratic base change of $\mathrm{GL}_2$, in the case where $L$ does not embed in $K_\infty$ over $K$, so that a real place of $K$ lies below a complex place of $L$; the matching is stated in terms of realised values of the integrals rather than of a single normalised measure. It is used by [`AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom`](thm.html#AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom), which packages the two clauses into the archimedean matching condition, and is obtained from the corresponding statement for norm conjugators equal to $1$ together with the transport of coupled Haar measures along $\sigma$-conjugation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧
      (∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δ) →
        ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ))
          (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
            (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
          Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
          ∃ I : ℂ,
            IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
              IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I) ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) := by sorry
