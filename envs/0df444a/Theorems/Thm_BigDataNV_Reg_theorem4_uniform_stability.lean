-- Prove2me | Theorems.Thm_BigDataNV_Reg_theorem4_uniform_stability
-- name    : BigDataNV.Reg.theorem4_uniform_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:19.590024+00:00
-- url     : https://prove2.me/theorems/ce6de9ab-a287-41bf-8a1f-fa3a44113ebf
-- title:
--   Theorem 4, p. 30 — (NV-reg) is uniformly stable with parameter (b∨h)²X²_max/(2nλ)
-- statement:
--   Let $b,h>0$ be the newsvendor costs, $\lambda>0$ the regularization parameter and $X_{\max}\ge0$. Let $S_n=\{(x_j,d_j)\}_{j=1}^n$ be a sample whose feature vectors satisfy $\|x_j\|_2^2\le X_{\max}^2$, and fix an index $i$. Let $\hat q$ minimize the (NV-reg) objective
--   $$\frac1n\sum_{j=1}^n C(q^\top x_j;d_j)+\lambda\|q\|_2^2$$
--   over $q\in\mathbb R^p$, and let $\hat q^{\setminus i}$ minimize the leave-one-out objective $\frac1n\sum_{j\ne i} C(q^\top x_j;d_j)+\lambda\|q\|_2^2$. Then for every feature vector $x$ with $\|x\|_2^2\le X_{\max}^2$ and every demand $d$,
--   $$\bigl|C(\hat q^\top x;d)-C((\hat q^{\setminus i})^\top x;d)\bigr|\le\frac{(b\vee h)^2X_{\max}^2}{2n\lambda}.$$
--
--   This is the uniform stability of (NV-reg) with parameter $\alpha_n^r=(b\vee h)^2X_{\max}^2/(2n\lambda)$, display (28). Together with the generalization bound for stable algorithms (Theorem 6), it yields the feature-count-free bound of Theorem 2.
--
--   **Formalization Note** The page writes the constant as $(b\vee h)^2/(2X_{\max}^{-2})\cdot 1/(n\lambda)$, i.e. a factor $X_{\max}^2$. The leave-one-out problem keeps the weight $1/n$, as in Theorem 5 (Bousquet and Elisseeff's (20)); running (NV-reg) literally on $n-1$ points would use $1/(n-1)$. The statement holds for any pair of minimizers. Symmetry of the algorithm is not stated, as the objective does not depend on the order of the sample. No bound on the demands is needed.
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), p. 30, Theorem 4, display (28); Definition 1, p. 28, display (24); proof p. 31

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

namespace BigDataNV.Reg

/-- Theorem 4, p. 30: (NV-reg) is uniformly stable with respect to the newsvendor cost, with
stability parameter `(b ∨ h)² X²_max / (2 n λ)`, in the form used by Theorem 5 (p. 31): the
comparison solution minimizes the leave-one-out objective with weight `1/n`. -/
theorem theorem4_uniform_stability {p n : ℕ} (b h lam Xmax : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (hS : ∀ j, ‖(S j).1‖ ^ 2 ≤ Xmax ^ 2)
    (i : Fin n) (q q' : EuclideanSpace ℝ (Fin p))
    (hq : IsNVRegSolution b h lam S q) (hq' : IsNVRegLooSolution b h lam S i q') :
    ∀ x : EuclideanSpace ℝ (Fin p), ‖x‖ ^ 2 ≤ Xmax ^ 2 → ∀ d : ℝ,
      |nvCost b h (inner ℝ q x) d - nvCost b h (inner ℝ q' x) d| ≤
        (max b h) ^ 2 * Xmax ^ 2 / (2 * (n : ℝ) * lam) := by sorry

end BigDataNV.Reg
