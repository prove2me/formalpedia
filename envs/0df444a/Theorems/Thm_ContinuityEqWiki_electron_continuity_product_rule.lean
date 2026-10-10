-- Prove2me | Theorems.Thm_ContinuityEqWiki_electron_continuity_product_rule
-- name    : ContinuityEqWiki.electron_continuity_product_rule
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:30.774414+00:00
-- url     : https://prove2.me/theorems/c6965398-c71b-4e68-9921-95009cf37292
-- title:
--   Semiconductor electron continuity equation (product-rule form)
-- statement:
--   Consider one-dimensional electron transport in a semiconductor. Let $n(t,x)$ be the electron concentration and $E(t,x)$ the electric field, let $e>0$ be the elementary charge, $\mu_n$ the electron mobility and $D_n$ the diffusion coefficient, and let $G_n(t,x)$, $R_n(t,x)$ be the generation and recombination rates. Assume $n(t,\cdot)$ is $C^2$ and $E(t,\cdot)$ is differentiable for every $t$. With the electron current density $J_n=e\,n\,\mu_nE+eD_n\frac{\partial n}{\partial x}$, suppose the conservation law
--   $$\frac{\partial n}{\partial t}=\frac1e\frac{\partial J_n}{\partial x}+(G_n-R_n)$$
--   holds everywhere. Then everywhere
--   $$\frac{\partial n}{\partial t}=\mu_nE\frac{\partial n}{\partial x}+\mu_n n\frac{\partial E}{\partial x}+D_n\frac{\partial^2n}{\partial x^2}+(G_n-R_n).$$
--
--   This is the final expression of the source's derivation, obtained by applying the product rule.
--
--   **Formalization Note** The source writes $d/dt$ and $d/dx$; since $n$ and $E$ depend on both $t$ and $x$, these are partial derivatives. The mobility and diffusion coefficient are constants.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Semiconductor", subsection "Derivation" (final expression)

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem electron_continuity_product_rule (e μ D : ℝ) (he : 0 < e) (n E G R : ℝ → ℝ → ℝ)
    (hn : ∀ t, ContDiff ℝ 2 (n t)) (hE : ∀ t, Differentiable ℝ (E t))
    (conservation : ∀ t x, deriv (fun s => n s x) t =
      1 / e * deriv (fun y => e * n t y * μ * E t y + e * D * deriv (n t) y) x
        + (G t x - R t x)) :
    ∀ t x, deriv (fun s => n s x) t =
      μ * E t x * deriv (n t) x + μ * n t x * deriv (E t) x + D * deriv (deriv (n t)) x
        + (G t x - R t x) := by sorry

end ContinuityEqWiki
