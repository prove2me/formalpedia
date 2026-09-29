-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_convexHull_subset_generalizedGradient
-- name    : ClarkeGradients.MaxFunctions.convexHull_subset_generalizedGradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:43:55.511773+00:00
-- url     : https://prove2.me/theorems/4e35cfe2-f4b2-4c3a-b7f7-f09194628de3
-- title:
--   (2.2) — co{∂ₓg(x, u) : u ∈ M(x)} ⊂ ∂f(x)
-- statement:
--   Let $U$ be a nonempty sequentially compact space and let $g:\mathbb R^n\times U\to\mathbb R$ satisfy hypotheses (a)–(d) of Theorem (2.1):
--
--   - **(a)** $g$ is upper semicontinuous in $(x,u)$;
--   - **(b)** $g$ is locally Lipschitz in $x$, uniformly for $u\in U$;
--   - **(c)** for all $x,u,v$, the one-sided derivative $g'_x(x,u;v)$ exists and equals $g^\circ_x(x,u;v)$;
--   - **(d)** $(x,u)\mapsto\partial_x g(x,u)$ is upper semicontinuous (sequential closed graph).
--
--   Here $\partial_x g(x,u)$, $g^\circ_x$ and $g'_x$ are the generalized gradient, the generalized directional derivative and the one-sided directional derivative of $y\mapsto g(y,u)$ at $x$. Let $f(x)=\max_{u\in U}g(x,u)$ and $M(x)=\{u:\ g(x,u)=f(x)\}$. Then for every $x\in\mathbb R^n$
--
--   $$
--   \operatorname{co}\{\partial_x g(x,u):\ u\in M(x)\}\subseteq\partial f(x),
--   $$
--
--   where co is the convex hull of the union of the sets $\partial_x g(x,u)$, $u\in M(x)$.
--
--   This is one half of assertion (4) of Theorem (2.1).
--
--   **Formalization Note** The inclusion is stated under all four hypotheses of Theorem (2.1), the setting in which the paper proves it; $U\neq\emptyset$ is explicit.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 252, proof of Theorem (2.1), Eq. (2.2)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), (2.2), in the proof of Theorem (2.1): under hypotheses (a)–(d),
`co {∂ₓg(x, u) : u ∈ M(x)} ⊆ ∂f(x)` for every `x`.
Here `U` is a nonempty sequentially compact space and
`f = maxFunction g`, `M(x) = maximizers g x`. -/
theorem convexHull_subset_generalizedGradient
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x) ⊆
        Shared.generalizedGradient (maxFunction g) x := by sorry

end ClarkeGradients.MaxFunctions
