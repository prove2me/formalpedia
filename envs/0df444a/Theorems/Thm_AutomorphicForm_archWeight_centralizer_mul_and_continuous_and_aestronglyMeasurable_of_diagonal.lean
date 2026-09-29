-- Prove2me | Theorems.Thm_AutomorphicForm_archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal
-- name    : AutomorphicForm.archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2211acb9-69df-55fc-a31a-1f6ac6183f36
-- title:
--   Invariance, continuity and measurability of the archimedean height weight
-- statement:
--   Let $K$ be a number field and let $\gamma \in \mathrm{GL}_2(\mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $\mathcal{O}_K$ over $K$. Write $\gamma_\infty =$ `AdelicLevel.glArch` $(\gamma) \in \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for its image under the map on $\mathrm{GL}_2$ induced by the projection of the adeles onto the infinite adeles. Assume that the matrix of $\gamma_\infty$ has vanishing $(1,0)$ and $(0,1)$ entries, i.e. is diagonal, and that $\gamma_\infty$ is regular semisimple in the sense of the project, namely that $\operatorname{tr}(\gamma_\infty)^2 - 4\det(\gamma_\infty)$ is a unit of $\mathbb{A}_{K,\infty}$. Let $\nu$ be an arbitrary measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of its topology. Consider the weight $W(y) = -\log H_\infty(y) - \log H_\infty(w_\infty y)$, where $H_\infty(g) = \prod_{v \mid \infty} \bigl(\lVert \det g_v\rVert / \mathrm{rowNormSq}(g_v)\bigr)^{\mathrm{mult}(v)}$ is the archimedean height, the product being over the infinite places of $K$ with $g_v$ the component of $g$ at $v$, and $w_\infty$ is the archimedean image of the global Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ of $\mathrm{GL}_2(K)$. The conclusion is the conjunction of three assertions: $W((t)x) = W(x)$ for every $t$ in the centraliser of $\{\gamma_\infty\}$ in $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and every $x \in \mathrm{GL}_2(\mathbb{A}_{K,\infty})$; $W$ is continuous; and the complex-valued function $x \mapsto (W(x) : \mathbb{C})$ is almost everywhere strongly measurable with respect to $\nu$.
--
--   This packages the three properties — left invariance under the centraliser of the regular diagonal archimedean component, continuity, and almost everywhere strong measurability — required of the archimedean log-height weight occurring in weighted orbital integrals on $\mathrm{GL}_2$ over the infinite adeles. It is used as the input verifying the weight hypotheses in the weighted Euler factorisation of class integrals and in the two comparisons of window brackets for weighted and twisted weighted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.archWeight_centralizer_mul_and_continuous_and_aestronglyMeasurable_of_diagonal
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hγ10 : (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (hγ01 : (AdelicLevel.glArch (𝓞 K) K γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ : AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K γ))
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))) :
    (∀ t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      ∀ x : GL (Fin 2) (InfiniteAdeleRing K),
        (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x) =
        (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) x) ∧
    Continuous (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) ∧
    AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)]
      (fun x => ((fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) x : ℂ)) ν := by sorry
