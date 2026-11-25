-- Prove2me | Theorems.Thm_Arxiv1901_08703_np_uniqueness
-- name    : Arxiv1901_08703.np_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:31:07.173353+00:00
-- url     : https://prove2.me/theorems/ffcbafcd-1652-40b0-bed5-9430fd94157e
-- title:
--   Theorem 2.1: the Neumann problem (NP) has at most one solution
-- statement:
--   Let $h\in C^2(\mathbb R)$ have compact support, let $k>0$, and let $f$ be a function on $\Gamma=\{(t,h(t))\}$. If $u$ and $v$ both solve the Neumann problem (NP) with data $f$, then $u=v$ in $D_+$.
--
--   Here a solution of (NP) is a function $u\in H^1_{loc}(D_+)$ that satisfies the Helmholtz equation $\Delta u+k^2u=0$ in $D_+$, the Sommerfeld radiation condition (1.3), and the Neumann condition $\partial u/\partial\nu=f$ on $\Gamma$ (eq. (2.1)), where $\nu$ is the unit normal directed into $D_+$. Equivalently, the only solution with $f=0$ is $u=0$.
--
--   **Formalization Note** A solution is taken in its representative that is $C^2$ in $D_+$. The condition $u\in H^1_{loc}(D_+)$ means $\int_{D_+\cap B_\rho}(|u|^2+|\nabla u|^2)\,dx<\infty$ for every $\rho$. The Neumann condition is imposed weakly: $\int_{D_+}(\nabla u\cdot\nabla\varphi-k^2u\varphi)\,dx=-\int_\Gamma f\varphi\,ds$ for every $\varphi\in C_c^\infty(\mathbb R^2)$. The radiation condition is the limit as $|x|\to\infty$ within $D_+$, which is uniform in the direction.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c001; Section 2, Theorem 2.1, eqs. (1.1), (1.3), (2.1), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem np_uniqueness (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : IsLocalProfile h) (f : ℝ → ℂ)
    (u v : R2 → ℂ) (hu : IsNPSolution k h f u) (hv : IsNPSolution k h f v) :
    ∀ x ∈ Dplus h, u x = v x := by sorry

end Arxiv1901_08703
