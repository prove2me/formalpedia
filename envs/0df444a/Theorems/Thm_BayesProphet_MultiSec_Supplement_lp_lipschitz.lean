-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_Supplement_lp_lipschitz
-- name    : BayesProphet.MultiSec.Supplement.lp_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:08:21.104815+00:00
-- url     : https://prove2.me/theorems/04eb3f9f-f977-468f-80ee-8a0c4aba54cd
-- title:
--   Proposition 2 — LP Lipschitz property of packing LP optimal solutions
-- statement:
--   Let $A\in\mathbb N^{d\times n}$ be a consumption matrix and let $\|\cdot\|_\mu$ be any norm on $\mathbb R^n$. For $b\in\mathbb R^d$, $r\in\mathbb R^n$ and $y\in\mathbb R^n_{\ge0}$ consider the LP
--   $$P(y):\qquad \max\{r'x:\ Ax\le b,\ 0\le x\le y\}.$$
--   Then there is a constant $\kappa=\kappa_\mu(A)$, depending only on $A$ and $\mu$, such that for every $b$, every $r$, all $y,\hat y\in\mathbb R^n_{\ge0}$ and every optimal solution $x$ of $P(y)$ there exists an optimal solution $\hat x$ of $P(\hat y)$ with
--   $$\|x-\hat x\|_\infty\ \le\ \kappa\,\|y-\hat y\|_\mu .$$
--
--   The statement is about the solution sets, not about a pair of selected optimizers: uniqueness is not assumed. It quantifies how the fluid solution $X^t$ (right-hand side $\mathbb E[Z(t)]$) and Offline's relaxation $X^{\star t}$ (right-hand side $Z(t)$) can be matched up, and it is the step that converts a deviation of the arrival counts into a deviation of LP solutions in the regret analyses of Theorems 3 and 5.
--
--   **Formalization Note** The norm is a Mathlib `Seminorm` on $\mathbb R^n$ together with definiteness ($\mu(y)=0\Rightarrow y=0$). $\|\cdot\|_\infty$ is Lean's sup norm on `Fin n → ℝ`. $\kappa$ is chosen after $A$ and $\mu$ and before $b$, $r$, $y$, $\hat y$, $x$.
--
--   Differences from the source:
--   - reading: the source writes "the LP" with an unspecified matrix $A$ → Lean takes the packing consumption matrix $A\in\mathbb N^{d\times n}$ of Section 2.1; reason: the proposition is stated for the packing LP of Eq. (4) (p. 20 "solutions $X^t$ and $X^{\star t}$"); for a general real matrix feasibility of $P(y)$ could depend on $y$ and the claim fails.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 20, Proposition 2

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Packing

namespace BayesProphet.MultiSec.Supplement

theorem lp_lipschitz {d n : ℕ} (A : Fin d → Fin n → ℕ) (μ : Seminorm ℝ (Fin n → ℝ))
    (hμ : ∀ y, μ y = 0 → y = 0) :
    ∃ κ : ℝ, IsLPLipschitzConst A μ κ := by sorry

end BayesProphet.MultiSec.Supplement
