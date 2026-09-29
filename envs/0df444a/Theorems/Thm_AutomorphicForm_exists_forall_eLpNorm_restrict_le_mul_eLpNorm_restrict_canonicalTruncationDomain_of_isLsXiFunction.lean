-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
-- name    : AutomorphicForm.exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ff3ade63-4aa0-5482-949a-1c48886085f4
-- title:
--   Compact-set L² bound by the truncation domain L² norm
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele class group units $(\mathbb{A}_K)^\times$ (i.e. of $(\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$) to $\mathbb{C}^\times$ whose associated scalar function $z \mapsto \xi_K(z) \in \mathbb{C}$ is continuous on $(\mathbb{A}_K)^\times$, and let $C$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Then there is a constant $c \in \mathbb{R}_{\ge 0}$, depending only on these data, such that for every function $b \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which satisfies $b(\gamma g)=b(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ (embedded via the map on general linear groups induced by $K \to \mathbb{A}_K$) and all $g$, and $b(zg) = \xi_K(z)\,b(g)$ for all ideles $z$ acting through the central scalar embedding $(\mathbb{A}_K)^\times \to \mathrm{GL}_2(\mathbb{A}_K)$, and which is almost everywhere strongly measurable for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ (taken with its Borel structure), one has the inequality of $\mathbb{R}_{\ge0}^\infty$-valued $L^2$ seminorms $$\lVert b \rVert_{L^2(C)} \le c \,\lVert b \rVert_{L^2(\Phi)},$$ the measures being the restrictions of `adelicGLHaar` to $C$ and to $\Phi =$ `canonicalTruncationDomain K α β`, the domain component of the canonical truncation datum attached to $K,\alpha,\beta$ (the empty set if no such datum exists). The constant $c$ is uniform in $b$.
--
--   This is the local-to-global $L^2$ comparison for automorphic functions: a compact set in $\mathrm{GL}_2(\mathbb{A}_K)$ meets only finitely many translates of the truncation domain, which by [`AutomorphicForm.canonicalTruncationData_isTruncationDatum`](thm.html#AutomorphicForm.canonicalTruncationData_isTruncationDatum) is a fundamental domain for $\mathrm{GL}_2(K)$ acting on the slab $\alpha \le \lVert \det g\rVert \le \beta$, so $L^2$ mass on compacta is controlled by $L^2$ mass on that domain. It is used to bound convolution operators acting on automorphic functions and to establish their continuity and decomposition properties on the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ c : ℝ≥0, ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ ξK b →
      AEStronglyMeasurable b (adelicGLHaar (Fin 2) (𝓞 K) K) →
      eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C) ≤
        (c : ℝ≥0∞) * eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (canonicalTruncationDomain K α β)) := by sorry
