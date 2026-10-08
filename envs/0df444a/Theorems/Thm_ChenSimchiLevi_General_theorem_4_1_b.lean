-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_theorem_4_1_b
-- name    : ChenSimchiLevi.General.theorem_4_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:53.981625+00:00
-- url     : https://prove2.me/theorems/b791bae4-46fb-4b8b-9b89-eaa42d6e3097
-- title:
--   Theorem 4.1(b): continuity, coercivity and a maximizing demand
-- statement:
--   Under Assumptions 1–5, for every period $t$, $g_t(y,d)$ is jointly continuous in inventory $y$ and admissible expected demand $d$. For each fixed admissible $d$, $g_t(y,d)\to-\infty$ as $|y|\to\infty$. At every fixed $y$ there is an expected demand level attaining the maximum over $[\underline d_t,\overline d_t]$:
--   $$\exists d_t(y)\in[\underline d_t,\overline d_t],\qquad g_t(y,d_t(y))=\max_{d\in[\underline d_t,\overline d_t]}g_t(y,d).$$
--   This result makes the paper's optimized profit function and best-price policy well-defined.
--
--   **Formalization Note** The printed phrase “continuous in $(y,p)$” is expressed in $(y,d)$, matching the theorem's own notation and the continuous price–expected-demand correspondence.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, Theorem 4.1(b)

import Definitions.Def_ChenSimchiLevi_General_Model

set_option autoImplicit false

namespace ChenSimchiLevi.General

open Filter

/-- Theorem 4.1(b), p. 891; the printed `(y,p)` is expressed in expected demand `d`. -/
theorem theorem_4_1_b (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ContinuousOn (fun q : ℝ × ℝ => M.g t q.1 q.2)
        (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) ∧
      (∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        Tendsto (fun y => M.g t y d) (cocompact ℝ) atBot) ∧
      (∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) := by sorry

end ChenSimchiLevi.General
