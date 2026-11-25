-- Prove2me | Theorems.Thm_Arxiv1901_08703_inverse_uniqueness
-- name    : Arxiv1901_08703.inverse_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:27:49.029204+00:00
-- url     : https://prove2.me/theorems/b19bbb14-f8da-5c97-aa94-a451cd64a1ec
-- title:
--   Theorem 4.3: the far-field patterns at one wave number determine the surface
-- statement:
--   Let $k>0$ and let $h_1,h_2\in C^2(\mathbb R)$ have compact support, with locally rough surfaces $\Gamma_j=\{x_2=h_j(x_1)\}$. For each $d\in\mathbb S^1_-$ let $u_j^s(\cdot;d)$ be the solution of (NP) for $\Gamma_j$ with data $-(\partial u^i/\partial\nu+\partial u^r/\partial\nu)$, where $u^i(x;d)=e^{ikd\cdot x}$, and let $u^\infty_j(\cdot;d)$ be its far-field pattern on $\mathbb S^1_+$. If $u^\infty_1(\hat x;d)=u^\infty_2(\hat x;d)$ for all $\hat x\in\mathbb S^1_+$ and all $d\in\mathbb S^1_-$, then $\Gamma_1=\Gamma_2$, i.e. $h_1=h_2$.
--
--   **Formalization Note** The scattering solutions and their far-field patterns are hypotheses of the statement. They exist by Theorem 2.7 and Remark 2.8.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c015; Section 4, Theorem 4.3, PDF p. 20

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem inverse_uniqueness (k : ℝ) (hk : 0 < k) (h1 h2 : ℝ → ℝ)
    (hh1 : IsLocalProfile h1) (hh2 : IsLocalProfile h2) (u1 u2 : R2 → R2 → ℂ)
    (hu1 : ∀ d : R2, IsLowerDir d → IsNPSolution k h1 (incData k d h1) (u1 d))
    (hu2 : ∀ d : R2, IsLowerDir d → IsNPSolution k h2 (incData k d h2) (u2 d))
    (F1 F2 : R2 → R2 → ℂ)
    (hF1 : ∀ d : R2, IsLowerDir d → HasFarFieldOn k (u1 d) (F1 d) upperCircle)
    (hF2 : ∀ d : R2, IsLowerDir d → HasFarFieldOn k (u2 d) (F2 d) upperCircle)
    (heq : ∀ d : R2, IsLowerDir d → ∀ xhat ∈ upperCircle, F1 d xhat = F2 d xhat) :
    h1 = h2 := by sorry

end Arxiv1901_08703
