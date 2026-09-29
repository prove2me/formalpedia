-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- name    : AutomorphicForm.exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/2c5e375e-0419-5c41-88cd-ece97a408e90
-- title:
--   Archimedean transfer for ramified quadratic base change of GL₂
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K] = 2$, let $\sigma$ be a non-trivial $K$-algebra automorphism of $L$, and assume there is no $K$-algebra homomorphism from $L$ into the infinite adele ring $K_\infty$ of $K$. Let `tysL` be an archimedean type family for $L$, that is, a number $\mathrm{card}\,w$ and a tuple of archimedean representations at $w$ for each infinite place $w$ of $L$, and let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be compactly supported and of the form $g \mapsto \Phi(\text{entries of } g)$ for some $\mathbb{R}$-smooth $\Phi$ on $2\times 2$ matrices over the mixed space of $L$ (the entries read through the identification of $L_\infty$ with that mixed space), and bi-finite for `tysL` in the sense that $g \mapsto \varphi_a(g^{-1})$ lies in `archFactorCutSubmodule` and $\varphi_a$ lies in `archFactorDualCutSubmodule` for `tysL`. Then there are an archimedean type family `tysK` for $K$ and a function $f_a$ on $\mathrm{GL}_2(K_\infty)$ with the same two properties over $K$ (smooth compactly supported entrywise form, and bi-finiteness for `tysK`) such that: (1) for every $\gamma \in \mathrm{GL}_2(K_\infty)$ with $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ a unit, every $\delta \in \mathrm{GL}_2(L \otimes_K K_\infty)$ whose $\sigma$-norm string equals the image of $\gamma$ exactly (conjugator $1$), and all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser of $\delta$, for their Borel structures, which are coupled in the sense that $\tau'$ and $\tau$ have the same image in $\mathrm{GL}_2(L \otimes_K K_\infty)$ under the inclusion and the base-change map, some single $I \in \mathbb{C}$ is simultaneously a realised value of the $\sigma$-twisted orbital integral of $\varphi_a$ composed with the identification $\mathrm{GL}_2(L \otimes_K K_\infty) \to \mathrm{GL}_2(L_\infty)$ at $\delta$ against the fixed Haar measure `archHaarL` and section datum $\tau'$, and a realised value of the orbital integral of $f_a$ at $\gamma$ against `archHaarK` and section datum $\tau$; and (2) for every such $\gamma$ that is not a $\sigma$-norm of any $\delta$ and every Haar $\tau$ on its centraliser, $0$ is a realised value of the orbital integral of $f_a$ at $\gamma$. Here a realised value means an integral $\int f(x^{-1}\gamma x)\,w(x)\,d\mu$ (respectively $\int \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,d\mu$) for some real weight $w$ satisfying the section condition `IsSectionFnOn` (respectively `IsTwistedSectionFnOn`); the assertion is thus the existence of a common realised value, not the equality of all values.
--
--   This is the archimedean half of the matching of (twisted) orbital integrals required for quadratic base change of $\mathrm{GL}_2$ in the ramified case, where a real place of $K$ lies below a complex place of $L$: a test factor on $\mathrm{GL}_2(L_\infty)$ is transferred to one on $\mathrm{GL}_2(K_\infty)$ whose orbital integrals match the twisted ones at norms and vanish at non-norms. It is used by [`AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom`](thm.html#AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom) in the construction of the archimedean component of the transferred test function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ 1 →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ))
          (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
            (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
          Coupled K L (InfiniteAdeleRing K) σ γ δ 1 τ τ' →
          ∃ I : ℂ,
            IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
              IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I) ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) := by sorry
