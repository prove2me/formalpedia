-- Prove2me | Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
-- name    : AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9bded6f5-82cd-52ac-a949-61dc26d104e5
-- title:
--   Adelic Siegel covering for GL₂ over a number field
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and write $\mathrm{GL}_2(\mathbb{A}_K)$ for the adelic group [`AutomorphicForm.AdelicGL2 (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L12). For real parameters $c,u,d_1,d_2$ the centre-cut Siegel set $\mathfrak{S}(c,u,d_1,d_2)$ consists of those $g \in \mathrm{GL}_2(\mathbb{A}_K)$ whose finite part `glFin` lies in the subgroup `finiteIntegralGL2` (the level-zero subgroup at the unit ideal) and which satisfy, at every infinite place $w$ of $K$, with $g_w$ the image of $g$ under `glArch` followed by `archComponent` at $w$: first $c \le \lVert \det g_w \rVert / \mathrm{rowNormSq}(g_w)$; second $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w) - (\lVert \det g_w \rVert/\mathrm{rowNormSq}(g_w))^2 \le u^2$; and third the archimedean determinant norm $\lVert \det g_w \rVert$ lies in the closed interval $[d_1,d_2]$. A subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ covers modulo the centre when for every $g$ there are $\gamma \in \mathrm{GL}_2(K)$ and $z \in \mathbb{A}_K^{\times}$ with $\mathrm{globalPoints}(\gamma)\, g\, \mathrm{centralScalar}(z) \in D$. The assertion is that there exist a finite set $T \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, a real $c > 0$ and a real $u$ such that for all reals $d_1, d_2$ with $0 < d_2$ and $d_1 \le d_2$, the union over $x \in T$ of the right translates $\mathfrak{S}(c,u,d_1,d_2)\,x$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre. The data $T$, $c$, $u$ are chosen once and serve every admissible determinant window simultaneously.
--
--   This is reduction theory for $\mathrm{GL}_2$ over a number field in adelic form: finitely many right translates of a single centre-cut Siegel set exhaust $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left multiplication by global points and right multiplication by the centre. It is the geometric input behind the volume, class-sum and compactness estimates for the adelic automorphic forms, and is cited by the growth bounds for class sums and by the compactness of the right-convolution operators on the cuspidal part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField

theorem AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K] :
    ∃ T : Finset (AutomorphicForm.AdelicGL2 (𝓞 K) K), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ,
      ∀ d₁ d₂ : ℝ, 0 < d₂ → d₁ ≤ d₂ →
        AutomorphicForm.SiegelCovering.CoversModCentre K
          (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂) := by sorry
