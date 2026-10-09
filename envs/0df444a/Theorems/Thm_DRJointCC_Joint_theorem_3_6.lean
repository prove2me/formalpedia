-- Prove2me | Theorems.Thm_DRJointCC_Joint_theorem_3_6
-- name    : DRJointCC.Joint.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:22.283542+00:00
-- url     : https://prove2.me/theorems/f9a46eae-122d-4f2c-8e9c-fded18e961a5
-- title:
--   Theorem 3.6, p. 20 — X°^JCC ⊆ ⋃_{α>0} Z^JCC(α) ⊆ X^JCC
-- statement:
--   Let $\tilde\xi\in\mathbb R^k$ be a random vector whose distribution is known only through its mean $\mu$ and covariance $\Sigma\succ0$, and let $\mathcal P$ be the set of all probability distributions with these moments. Let $\epsilon\in(0,1)$ and consider $m\ge1$ constraints $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$ whose coefficients depend affinely on a decision $x\in\mathbb R^n$. Define
--
--   1. the robust joint chance constraint set $\mathcal X^{\mathrm{JCC}}=\{x:\inf_{\mathbb P\in\mathcal P}\mathbb P(y_i^0(x)+y_i(x)^\top\tilde\xi\le0\ \forall i)\ge1-\epsilon\}$;
--   2. its strict version $\mathcal X^{\mathrm{JCC}}_\circ=\{x:\inf_{\mathbb P\in\mathcal P}\mathbb P(\bigcap_i\{y_i^0(x)+y_i(x)^\top\tilde\xi<0\})\ge1-\epsilon\}$;
--   3. the worst-case CVaR approximation with optimized scaling parameters $\mathcal Z^{\mathrm{JCC}}=\bigcup_{\alpha>0}\mathcal Z^{\mathrm{JCC}}(\alpha)$, where $\mathcal Z^{\mathrm{JCC}}(\alpha)=\{x:\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon(\max_i\alpha_i(y_i^0(x)+y_i(x)^\top\tilde\xi))\le0\}$.
--
--   Then
--   $$
--   \mathcal X^{\mathrm{JCC}}_\circ\subseteq\mathcal Z^{\mathrm{JCC}}\subseteq\mathcal X^{\mathrm{JCC}}.
--   $$
--
--   The worst-case CVaR approximation of a distributionally robust joint chance constraint is thus essentially exact when the scaling parameters are treated as decision variables: it is squeezed between the robust constraint and its strict version.
--
--   **Formalization Note** The union is over componentwise strictly positive $\alpha$ (the page prints $\bigcup_{\alpha\in\mathcal S}$; $\mathcal S$ is read as $\mathcal A$ of p. 15). CVaR and the worst-case CVaR are extended-real valued, so no junk value of a real supremum enters. $m\ge1$ (implicit in the maximum over $i$), $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses. No nondegeneracy assumption on the constraint functions is made.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 20, Theorem 3.6

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- Theorem 3.6, p. 20: the worst-case CVaR approximation is essentially exact when the scaling
parameters are decision variables: `X°^JCC ⊆ Z^JCC ⊆ X^JCC`. -/
theorem theorem_3_6 {m n k : ℕ} (hm : 0 < m) (D : JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    XJCCStrict D μ Sig ε ⊆ ZJCC D μ Sig ε ∧ ZJCC D μ Sig ε ⊆ XJCC D μ Sig ε := by sorry

end DRJointCC.Joint
