-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_corollary_1
-- name    : FMLPricing.BranchBound.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:54.652528+00:00
-- url     : https://prove2.me/theorems/d2b9ef12-6f3b-4a15-9068-22378a716354
-- title:
--   Corollary 1, p. 17 — χ of an LP(x, r) solution lies in R(x, r) ∩ X, and equals x when x ∈ X
-- statement:
--   Let $x \in \mathbb R^m$ have positive entries, let $r > 0$, and suppose $R(x, r) \cap X \neq \emptyset$. Let $(\gamma, z, \delta^+, \delta^-)$ be a solution (a minimizer of $\gamma$) of $\mathrm{LP}(x, r)$, and let
--   $$
--   \chi(x, \delta^+, \delta^-) = \Big( \frac{x_1}{1 + x_1(\delta^-_1 - \delta^+_1)}, \dots, \frac{x_m}{1 + x_m(\delta^-_m - \delta^+_m)} \Big).
--   $$
--   Then
--   $$
--   \chi(x, \delta^+, \delta^-) \in R(x, r) \cap X, \tag{18}
--   $$
--   and, if moreover $x \in X$, then $\chi(x, \delta^+, \delta^-) = x$ (19).
--
--   In Algorithm 1 this produces, from each surviving center $x$, an attainable point $x^\delta$ in the box. Because $x^\delta \in R(x, r)$, the enlarged radius $r^\delta = r + \|x - x^\delta\|_\infty$ is at most $2r$.
--
--   **Formalization Note** As in Proposition 7, $x \in (0,1)^m$ is relaxed to $x_c > 0$, and $\mathrm{LP}(x, r)$ uses the two-sided form of constraints (15)–(16).
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 17, Corollary 1 and the definition of χ (proof pp. 43–44)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Corollary 1, p. 17, for every `x` with positive entries: a solution of `LP(x, r)` gives
`χ(x, δ⁺, δ⁻) ∈ R(x, r) ∩ X` (18), and `χ(x, δ⁺, δ⁻) = x` when `x ∈ X` (19). -/
theorem corollary_1 {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x : Fin m → ℝ) (hx : ∀ c, 0 < x c) (r : ℝ) (hr : 0 < r)
    (hR : (Rbox I x r ∩ Xset I).Nonempty) (v : LPVars m n) (hv : IsLPSolution I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I ∧ (x ∈ Xset I → chi x v.δp v.δm = x) := by sorry

end FMLPricing.BranchBound
