-- Prove2me | Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
-- name    : AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/be7a408b-10d3-5317-984b-6c2b2ee768a5
-- title:
--   Finite Haar volume of a determinant slab inside a twisted-centraliser tube
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $D$ be an idèle-theoretic Galois descent datum for $\mathcal{O}_L \subseteq L$ over $K$, that is, a monoid homomorphism from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adèle ring $\mathbb{A}_L$, compatible with $\mathrm{Gal}$-action on $L$ through $\mathrm{algebraMap}$ and continuous in each argument. Write $G = \mathrm{GL}_2(\mathbb{A}_L)$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, let $\sigma_{\mathbb{A}}$ denote the entrywise action of $D.\mathrm{act}\,\sigma$ on $G$, and for $s \in \mathrm{GL}_2(L)$ let $\iota(s) \in G$ be its image under the entrywise map induced by $L \to \mathbb{A}_L$. Fix reals $\alpha, \beta$ with $0 < \alpha$, a compact set $C \subseteq G$, and a measurable set $F \subseteq G$ contained in the slab $\{g : \|\det g\| \in [\alpha, \beta]\}$, where $\|\cdot\|$ is the idèle norm given by the value of the distributive Haar character of $\mathbb{A}_L$, viewed in $\mathbb{R}$. Assume that for all distinct $s, s' \in \mathrm{GL}_2(L)$ with $s^{-1}\sigma(s)$ and $s'^{-1}\sigma(s')$ scalar matrices (each equal to $\mathrm{scalar}\,u$ for some $u \in L^{\times}$) the intersection $\iota(s)F \cap \iota(s')F$ is Haar-null. Then the Haar measure of $F \cap \{g : g = g_1 k$ for some $g_1 \in G$ with $g_1^{-1}\sigma_{\mathbb{A}}(g_1)$ in the centre of $G$ and some $k \in C\}$ is finite.
--
--   This is the finiteness estimate that makes Weil's quotient integral formula applicable to the twisted centraliser $G_1 = \{g : g^{-1}\sigma_{\mathbb{A}}(g) \in Z(G)\}$ of $\mathrm{GL}_2(\mathbb{A}_L)$: an almost-disjointly $\mathrm{GL}_2(L)$-packed Borel set lying in a determinant slab has finite volume once it is cut down to a tube $G_1C$ with compact cross-section. It is used in the convergence statement for the twisted kernel attached to the identity family, [`AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top`](thm.html#AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_identityFamily_lt_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (hα : 0 < α)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C)
    (F : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hFs : F ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFm : MeasurableSet F)
    (hF : ∀ s s' : GL (Fin 2) L,
      (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
      s ≠ s' →
        adelicGLHaar (Fin 2) (𝓞 L) L
          (AutomorphicForm.globalPoints (𝓞 L) L s • F ∩
            AutomorphicForm.globalPoints (𝓞 L) L s' • F) = 0) :
    adelicGLHaar (Fin 2) (𝓞 L) L
        (F ∩ {g | ∃ g₁ k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
          g₁⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g₁ ∈
              Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
            k ∈ C ∧ g = g₁ * k}) < ⊤ := by sorry
