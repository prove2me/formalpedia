-- Prove2me | Theorems.Thm_CurvatureSubmod_CSSP_lemma_8_1_monotone
-- name    : CurvatureSubmod.CSSP.lemma_8_1_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:52.537116+00:00
-- url     : https://prove2.me/theorems/b085da2f-4d97-4863-887d-84cfcde4f92d
-- title:
--   Lemma 8.1, p. 11 (monotone part) — S ↦ ‖proj_S(v)‖² is monotone increasing
-- statement:
--   Let $c_1, \dots, c_n$ be vectors in $\mathbb{R}^m$ and let $v \in \mathbb{R}^m$ be arbitrary. For $S \subseteq [n]$ let $\mathrm{proj}_S(v)$ be the orthogonal projection of $v$ onto $\mathrm{span}\{c_i : i \in S\}$. Then the set function
--   $$F(S) = \|\mathrm{proj}_S(v)\|^2$$
--   is monotone increasing: $F(S + i) - F(S) \ge 0$ for all $S \subseteq [n]$ and $i \in [n]$.
--
--   This is the monotonicity half of Lemma 8.1. Enlarging $S$ enlarges the subspace, so the projection captures at least as much of $v$.
--
--   **Formalization Note** Lemma 8.1 as printed also asserts that $F$ is submodular. That half is false and is not stated: with $c_1 = e_1$, $c_2 = e_1 + e_2$ in $\mathbb{R}^2$ and $v = e_2$ one gets $F(\{1,2\}) + F(\emptyset) = 1 > \tfrac12 = F(\{1\}) + F(\{2\})$. Monotonicity is the marginal form of §2.1.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 11, Lemma 8.1 (monotonicity part)

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting

namespace CurvatureSubmod.CSSP

/-- Lemma 8.1, p. 11, its monotonicity half: `S ↦ ‖proj_S(v)‖²` is monotone increasing.
The printed submodularity half is false (columns `e₁, e₁ + e₂`, `v = e₂`) and is not stated. -/
theorem lemma_8_1_monotone {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) :
    MonoInc (fun S : Finset (Fin n) => ‖proj c S v‖ ^ 2) := by sorry

end CurvatureSubmod.CSSP
