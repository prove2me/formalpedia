-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_proposition_7
-- name    : FMLPricing.BranchBound.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:49.020547+00:00
-- url     : https://prove2.me/theorems/b6c9463e-cd74-49f9-9025-7adea7e96756
-- title:
--   Proposition 7, p. 16 — the box R(x, r) meets X exactly when LP(x, r) is feasible
-- statement:
--   Let $x \in \mathbb R^m$ have positive entries and let $r > 0$. Then
--   $$
--   R(x, r) \cap X \neq \emptyset \iff \mathrm{LP}(x, r) \text{ is feasible},
--   $$
--   where $\mathrm{LP}(x, r)$ has the variables $(\gamma, z, \delta^+, \delta^-)$, $\delta^\pm \ge 0$, and the constraints $\sum_j s_{cj} z_j + \delta^+_c - \delta^-_c = \mu_c(x)$, $\gamma \ge \delta^+_c + \delta^-_c$, $\mu_c(\bar x_c(x,r)) \le \mu_c(x) - \delta^+_c + \delta^-_c \le \mu_c(\underline x_c(x,r))$ and $\underline z \le z \le \bar z$.
--
--   Algorithm 1 uses this to discard boxes that contain no attainable vector of no-purchase probabilities.
--
--   **Formalization Note** Two departures from the page, both needed for a true statement that Algorithm 1 can use. (i) The page assumes $x \in (0,1)^m$; here $x_c > 0$ suffices, which is stronger, and Algorithm 1's centers can have entries above $1$. (ii) Constraints (15)–(16) are taken in the two-sided form that the paper's proof (p. 43) derives from them. With the printed one-sided form $\delta^+_c \le \mu_c(x) - \mu_c(\bar x_c(x,r))$, $\delta^-_c \le \mu_c(\underline x_c(x,r)) - \mu_c(x)$, the direction "$\Rightarrow$" fails whenever $x_c > q_{c0}(\bar p)$ or $x_c < q_{c0}(\underline p)$. For example, take $m = n = 1$, $a = 0$, $b = 1$, $x = 0.8$, $r = 0.05$: then $R(x, r) = [0.75, 0.782]$ meets $X = [0.731, 0.782]$, but the printed (15) requires $\delta^+ \le -0.028$. For $\underline x(x, r) \le x \le \bar x(x, r)$ the printed LP's feasible points are feasible here.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 16, Proposition 7 and LP(x, r) (13)–(17) (proof pp. 42–43)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Proposition 7, p. 16, for every `x` with positive entries: `R(x, r) ∩ X ≠ ∅` if and
only if `LP(x, r)` is feasible (constraints (15)–(16) in their two-sided form). -/
theorem proposition_7 {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x : Fin m → ℝ) (hx : ∀ c, 0 < x c) (r : ℝ) (hr : 0 < r) :
    (Rbox I x r ∩ Xset I).Nonempty ↔ LPFeasible I x r := by sorry

end FMLPricing.BranchBound
