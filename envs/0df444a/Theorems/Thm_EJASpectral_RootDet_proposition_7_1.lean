-- Prove2me | Theorems.Thm_EJASpectral_RootDet_proposition_7_1
-- name    : EJASpectral.RootDet.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:59.548957+00:00
-- url     : https://prove2.me/theorems/9fce6579-ed58-40c0-ba3a-d2a020f78263
-- title:
--   Proposition 7.1, p. 24 — Γ(u,w) = −log(det(w)^{1/d} − u) − logdet(w) is a (1 + d)-LHSCB for the root-determinant cone
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$ and determinant $\det$. Let
--   $$\mathcal K_{\mathrm{rtdet}} = \{(u,w)\in\mathbb R\times\mathcal Q : u\le\det(w)^{1/d}\}$$
--   be the root-determinant cone (98a). Then $\mathcal K_{\mathrm{rtdet}}$ is a proper cone, and
--   $$\Gamma(u,w) = -\log\big(\det(w)^{1/d} - u\big) - \log\det(w) \tag{102}$$
--   is a **$(1+d)$-logarithmically homogeneous self-concordant barrier** for $\mathcal K_{\mathrm{rtdet}}$: $\Gamma$ is $C^3$ and convex on $\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$, tends to $+\infty$ at the boundary from inside, satisfies $\Gamma(\theta\tilde u) = \Gamma(\tilde u) - (1+d)\log\theta$ for $\theta>0$, and satisfies $|\nabla^3\Gamma(\tilde u)[\tilde p,\tilde p,\tilde p]|\le 2(\nabla^2\Gamma(\tilde u)[\tilde p,\tilde p])^{3/2}$ for all $\tilde u\in\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$ and $\tilde p\in\mathbb R\times V$.
--
--   The barrier parameter $1+d$ exceeds the optimal parameter $d$ of the domain $\mathbb R\times\mathcal Q$ by one. The result lets interior-point methods handle the hypograph of the geometric mean of eigenvalues (for $V=\mathbb S^d$, of $\det(W)^{1/d}$) natively, with the iteration bound $O(\sqrt{1+d}\,\log(1/\varepsilon))$.
--
--   **Formalization Note** $V$ is an abstract Euclidean Jordan algebra carrying its spectral decomposition (see the definition `EJA`), not a specific matrix algebra. The hypothesis $d\ge1$ is added: the paper divides by $d$, and at $d=0$ the statement is false. Properness of the cone is part of the conclusion because the paper's definition of an LHB (p. 12) is for a proper cone and p. 23 asserts that $\mathcal K_{\mathrm{rtdet}}$ is proper. Logarithmic homogeneity is stated for $\tilde u\in\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$, $\theta>0$, and self-concordance includes convexity (Nesterov–Nemirovskii Definitions 2.1.1, 2.3.2).
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, Proposition 7.1

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- Proposition 7.1, p. 24: `Γ(u, w) = −log(det(w)^{1/d} − u) − logdet(w)` in (102) is a
`(1 + d)`-LHSCB for the proper cone `K_rtdet` in (98a). -/
theorem proposition_7_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    IsProperCone (Krtdet J) ∧ IsLHSCB (Krtdet J) (Gamma J) (1 + (d : ℝ)) := by sorry

end EJASpectral.RootDet
