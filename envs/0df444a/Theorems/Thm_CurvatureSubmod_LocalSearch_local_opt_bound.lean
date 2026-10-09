-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_local_opt_bound
-- name    : CurvatureSubmod.LocalSearch.local_opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:05.356062+00:00
-- url     : https://prove2.me/theorems/e1b683a0-f64e-464a-9dbd-5d23d5aa2333
-- title:
--   §5.1, p. 7 — a swap-local optimum $S$ of $\psi$ has $g(S)+\ell(S) \ge (1-e^{-1})g(O)+\ell(O)$ for every base $O$
-- statement:
--   Let $X$ be a finite set, $g : 2^X \to \mathbb{R}_{\ge 0}$ monotone increasing and submodular, $\ell(A) = \sum_{j \in A} w(j)$ linear with arbitrary real weights, and $\psi = (1 - e^{-1}) h + \ell$ with $h$ the Filmus–Ward potential of $g$. Let $\mathcal M$ be a matroid on $X$ and $S$ a base of $\mathcal M$ that is locally optimal for $\psi$ under single-element exchanges: $\psi(S - a + b) \le \psi(S)$ whenever $a \in S$, $b \notin S$ and $S - a + b$ is a base. Then for every base $O$ of $\mathcal M$,
--   $$g(S) + \ell(S) \ \ge\ (1 - e^{-1})\, g(O) + \ell(O).$$
--
--   This is the exact ($\delta = 0$) form of the guarantee required by Theorem 3.1, obtained from the local search of §5.
--
--   **Formalization Note** "Locally optimal" is Figure 4's stopping rule with $\delta = 0$ (`IsSwapLocalOpt`). As in Lemma 5.2, $g$ is monotone and nonnegative.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 7, §5.1, paragraph after the proof of Lemma 5.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- §5.1, p. 7 (paragraph after the proof of Lemma 5.2): a swap-local optimum `S` of `ψ`
satisfies `g(S) + ℓ(S) ≥ (1 − e^{−1}) g(O) + ℓ(O)` for every base `O`. -/
theorem local_opt_bound {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (w : X → ℝ) (M : Matroid X) (S : Finset X) (hS : IsSwapLocalOpt M (psi g w) S)
    (O : Finset X) (hO : M.IsBase (↑O : Set X)) :
    (1 - Real.exp (-1)) * g O + linFun w O ≤ g S + linFun w S := by sorry

end CurvatureSubmod.LocalSearch
