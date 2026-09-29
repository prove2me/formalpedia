-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_generalizedGradient_maxFunction_eq
-- name    : ClarkeGradients.MaxFunctions.generalizedGradient_maxFunction_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:44:55.946724+00:00
-- url     : https://prove2.me/theorems/9b493e86-4bdb-4e3c-9869-f34d62026c42
-- title:
--   Theorem (2.1)(4) — ∂f(x) = co{∂ₓg(x, u) : u ∈ M(x)}
-- statement:
--   Let $U$ be a nonempty sequentially compact space and let $g:\mathbb R^n\times U\to\mathbb R$ satisfy hypotheses (a)–(d) of Theorem (2.1) (upper semicontinuity of $g$ in $(x,u)$; local Lipschitz continuity in $x$ uniform in $u$; $g'_x(x,u;\cdot)$ exists and equals $g^\circ_x(x,u;\cdot)$ for all $x,u$; upper semicontinuity of $(x,u)\mapsto\partial_x g(x,u)$). Let $f(x)=\max_{u\in U}g(x,u)$ and $M(x)=\{u:\ g(x,u)=f(x)\}$. Then for every $x\in\mathbb R^n$
--
--   $$
--   \partial f(x)=\operatorname{co}\{\partial_x g(x,u):\ u\in M(x)\}.
--   $$
--
--   The generalized gradient of a max function is the convex hull of the generalized gradients of the active pieces. This is assertion (4) of Theorem (2.1), proved in the paper before (2) and (3), which follow from it.
--
--   **Formalization Note** The right side is `convexHull ℝ (⋃ u ∈ M x, ∂ₓg x u)`: the plain convex hull, as printed, with no closure.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 251, Theorem (2.1), assertion (4); proof p. 252

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1), assertion (4): under hypotheses (a)–(d),
`∂f(x)` is the convex hull of `{∂ₓg(x, u) : u ∈ M(x)}`.
Here `U` is a nonempty sequentially compact space and
`f = maxFunction g`, `M(x) = maximizers g x`. -/
theorem generalizedGradient_maxFunction_eq
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
      Shared.generalizedGradient (maxFunction g) x =
        convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x) := by sorry

end ClarkeGradients.MaxFunctions
