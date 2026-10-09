-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_theorem_6_1_local_opt
-- name    : CurvatureSubmod.LocalSearch.theorem_6_1_local_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:08.012775+00:00
-- url     : https://prove2.me/theorems/ccf887ee-8e8c-47ce-b46e-27eeafbf9647
-- title:
--   Theorem 6.1, exact core (ε = 0), p. 8 — every swap-local optimum $S$ of $\psi$ has $f(S) \ge (1 - c/e) f(O)$ for all $O \in \mathcal I$
-- statement:
--   This is the exact core ($\epsilon = 0$) of Theorem 6.1, for swap-local optima of $\psi$.
--
--   Let $X$ be a finite set and $f : 2^X \to \mathbb{R}_{\ge 0}$ a monotone increasing submodular function with total curvature at most $c \in [0,1]$, i.e. $f_{X-j}(j) \ge (1-c) f_\emptyset(j)$ for every $j \in X$. Let $\mathcal M = (X, \mathcal I)$ be a matroid on $X$. Decompose $f$ as in §6.1,
--   $$\ell(A) = \sum_{j \in A} f_{X-j}(j), \qquad g(A) = f(A) - \ell(A),$$
--   let $h$ be the Filmus–Ward potential of $g$ and $\psi(A) = (1 - e^{-1}) h(A) + \ell(A)$. If $S$ is a base of $\mathcal M$ that no single swap $S - a + b$ ($a \in S$, $b \in X \setminus S$, $S - a + b$ a base) improves in $\psi$, then for every independent set $O \in \mathcal I$,
--   $$f(S) \ \ge\ \Bigl(1 - \frac{c}{e}\Bigr)\, f(O).$$
--
--   The factor $1 - c/e$ interpolates between $1$ for linear functions ($c = 0$) and the classical $1 - 1/e$ for general monotone submodular functions ($c = 1$), and Theorem 7.1 shows it is optimal in the value-oracle model.
--
--   **Formalization Note** The printed Theorem 6.1 asserts a randomized polynomial-time algorithm with loss $O(\epsilon)$; only the exact statement about local optima, which is what its proof establishes for $\epsilon = 0$, is posed. The local optimality of $S$ is essential: without it the claim is trivial (take $S$ optimal). $f$ need not satisfy $f(\emptyset) = 0$. Curvature is in product form. The matroid's ground set is the whole of $X$ (`M.E = Set.univ`).
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 8, Theorem 6.1 and its proof (pp. 8–9), with §5.1 (p. 7)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Exact core (ε = 0) of Theorem 6.1, p. 8 (proof pp. 8–9, with §5.1, p. 7): every swap-local
optimum `S` of `ψ = (1 − e^{−1}) h + ℓ`, built from the decomposition `f = g + ℓ` of §6.1,
satisfies `f(S) ≥ (1 − c/e) f(O)` for every independent set `O`. -/
theorem theorem_6_1_local_opt {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcurv : CurvAtMostInc f c)
    (M : Matroid X) (hE : M.E = Set.univ)
    (S : Finset X) (hS : IsSwapLocalOpt M (psi (gMax f) (wMax f)) S)
    (O : Finset X) (hO : M.Indep (↑O : Set X)) :
    (1 - c * Real.exp (-1)) * f O ≤ f S := by sorry

end CurvatureSubmod.LocalSearch
