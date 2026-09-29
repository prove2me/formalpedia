-- Prove2me | Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
-- name    : AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6d68d4b1-be76-50fe-96bf-a3297ccf7de3
-- title:
--   Central character of a non-zero continuous L_{s,ξ}-function
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K`. Let $\chi$ be a group homomorphism from the full subgroup $\top$ of the idele group $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ (no continuity assumed), and let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a function on `AdelicGL2 (𝓞 K) K`, the general linear group of $2\times 2$ matrices over $\mathbb{A}_K$. Assume `IsLsXiFunction (𝓞 K) K ⊤ χ φ`, that is: $\varphi(\gamma g) = \varphi(g)$ for every $\gamma \in \mathrm{GL}_2(K)$, pushed into $\mathrm{GL}_2(\mathbb{A}_K)$ by the structure map $K \to \mathbb{A}_K$ applied entrywise, and every $g$; and $\varphi(zg) = \chi(z)\varphi(g)$ for every idele $z$, embedded as the scalar matrix $\mathrm{diag}(z,z)$, and every $g$. Assume also that $\varphi$ is continuous and that $\varphi(g) \neq 0$ for some $g$. The conclusion is twofold: first, $\chi$ takes the value $1$ at the image of every $u \in K^\times$ under the map of unit groups induced by $K \to \mathbb{A}_K$; second, the map $z \mapsto \chi(z)$ on $\mathbb{A}_K^\times$ is continuous, the target $\mathbb{C}^\times$ carrying its topology as a group of units.
--
--   This is the standard fact that the central character of a non-zero automorphic form, here of a continuous function on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying left $\mathrm{GL}_2(K)$-invariance and a central transformation law, is a continuous character of $\mathbb{A}_K^\times$ trivial on the principal ideles, i.e. an idele class character. It is used throughout the analytic part of the development, for instance by the estimates on $L^2$-norms of such functions over fundamental domains modulo the centre and by the construction of cuspidal isotypic vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    (∀ u : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ := by sorry
