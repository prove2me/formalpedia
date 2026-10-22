-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_tangential_hessian
-- name    : BirkhoffGlobalSection.eh_half_mass_tangential_hessian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T12:42:48.875259+00:00
-- url     : https://prove2.me/theorems/e111377c-8f8a-4718-a425-acfc2c36e4cd
-- title:
--   Equal-mass EH zero level has positive tangential Hessian
-- statement:
--   Fix equal masses $\mu=\tfrac12$ and an energy $c>2$. Let $G_c$ be the centered-left elliptic-hyperbolic Hamiltonian `ehLeftHamiltonian (1/2) c`. At every point $s=(x_1,x_2,y_1,y_2)$ with
--
--   $$G_c(s)=0,\qquad |x_2|\le\frac{\pi}{2},\qquad \cosh^2x_1\le 2c,$$
--
--   the tangential Hessian is positive:
--
--   $$dG_c(s)\,v=0,\ v\ne0\ \Longrightarrow\ D^2G_c(s)[v,v]>0 .$$
--
--   This is Liu--Salomão, Theorem 9.4(ii), on the left Hill box. Write $G_c=\tfrac12|y+F|^2+V$, with $y_F=y+F=r(\cos\theta,\sin\theta)$ and $U=r(\cos\theta\,\nabla^2f_1+\sin\theta\,\nabla^2f_2)+\nabla^2V=\operatorname{diag}(c_t,d_s)$. For $v=(\xi,\eta)$, put $\zeta=\eta+\nabla F\,\xi$. Then the Hessian is
--
--   $$D^2G[v,v]=|\zeta|^2+\xi^{T}U\xi,$$
--
--   and the tangency condition reads $y_F\cdot\zeta=-\nabla V\cdot\xi$.
--
--   So positivity is equivalent to positive definiteness of $r^2U+\nabla V\otimes\nabla V$, which is $\det U_W>0$ in Theorem 9.1. On the Hill boundary $r=0$ it reduces to $(\nabla V J)\nabla^2V(\nabla VJ)^T>0$.
--
--   Liu--Salomão prove $c_t>0$ (Lemma 9.6) and $\det U_W>0$ for all $h\le-2$ by a monotonicity argument in $h$. Numerically, $\det U_W/(|\nabla V|^2+r^2)^2$ has minimum $0.026$ at $c=2.0001$, and the minimum tends to $1$ as $c\to\infty$.
--
--   With the published perturbation module `BirkhoffGlobalSection_EHConvexPerturbation`, this statement gives `eh_left_tangential_hessian_positive`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) with the criterion of Theorem 9.1 (positive tangential Hessian iff det U_W > 0) and the monotonicity argument of Lemmas 9.6-9.7; equal masses, energies h = -c < -2.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Equal masses, every subcritical energy `c > 2`: the centered-left EH
Hamiltonian has positive tangential Hessian on its zero level inside the left
Hill box `|x₂| ≤ π/2`, `cosh² x₁ ≤ 2c` (Liu--Salomão, Theorem 9.4(ii)). -/
theorem eh_half_mass_tangential_hessian (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c)
    (v : Phase) (hv : v ≠ 0) (htan : fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian (1 / 2) c) x v) s v := by sorry

end BirkhoffGlobalSection
