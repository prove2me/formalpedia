-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_maxFunction_lipschitzOnBounded
-- name    : ClarkeGradients.MaxFunctions.maxFunction_lipschitzOnBounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:43:14.752004+00:00
-- url     : https://prove2.me/theorems/1056ee80-ff9b-48e4-bbe4-e0f881a41a6f
-- title:
--   Theorem (2.1)(1) — the max function is locally Lipschitz
-- statement:
--   Let $U$ be a nonempty sequentially compact topological space and $g:\mathbb R^n\times U\to\mathbb R$ satisfy
--
--   - **(a)** $g(x,u)$ is upper semicontinuous in $(x,u)$;
--   - **(b)** $g$ is locally Lipschitz in $x$, uniformly for $u\in U$: for every bounded $B\subseteq\mathbb R^n$ there is one constant $K$ with $|g(x_1,u)-g(x_2,u)|\le K|x_1-x_2|$ for all $x_1,x_2\in B$ and **all** $u\in U$.
--
--   Then the max function $f(x)=\max\{g(x,u):u\in U\}$ is locally Lipschitz (Lipschitz on every bounded set).
--
--   This is the first assertion of Theorem (2.1); the rest of that theorem is about $\partial f$ and $f^\circ$, which are meaningful only because $f$ is locally Lipschitz.
--
--   **Formalization Note** Only hypotheses (a) and (b) of Theorem (2.1) are assumed, since the paper's proof of (1) uses only these, the sequential compactness of $U$, and $U\neq\emptyset$ (which the paper uses implicitly in "max" and makes explicit here as `[Nonempty U]`). The max is `⨆ u, g x u`.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 251, Theorem (2.1), assertion (1); proof p. 252

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1), assertion (1): if `U` is a nonempty sequentially compact
space, `g(x, u)` is upper semicontinuous in `(x, u)` (hypothesis (a)) and `g` is locally
Lipschitz in `x` uniformly for `u ∈ U` (hypothesis (b)), then `f(x) = max_u g(x, u)` is
locally Lipschitz. -/
theorem maxFunction_lipschitzOnBounded
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B) :
    Shared.LipschitzOnBounded (maxFunction g) := by sorry

end ClarkeGradients.MaxFunctions
