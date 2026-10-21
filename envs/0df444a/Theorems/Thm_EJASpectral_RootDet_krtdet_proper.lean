-- Prove2me | Theorems.Thm_EJASpectral_RootDet_krtdet_proper
-- name    : EJASpectral.RootDet.krtdet_proper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:51.567987+00:00
-- url     : https://prove2.me/theorems/2e49406c-2cf1-4703-895c-00c96fd4915a
-- title:
--   p. 23 — the root-determinant cone K_rtdet is a proper cone
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$. The root-determinant cone
--   $$\mathcal K_{\mathrm{rtdet}} = \{(u,w)\in\mathbb R\times\mathcal Q : u\le\det(w)^{1/d}\}$$
--   is a **proper cone** in $\mathbb R\times V$: it is closed, convex, closed under nonnegative scaling, pointed, and has nonempty interior.
--
--   Properness is the standing requirement on a cone that carries a logarithmically homogeneous barrier (p. 12), and it is part of the goal theorem.
--
--   **Formalization Note** The paper says "primitive proper cone"; primitivity (not a Cartesian product of lower-dimensional proper cones, p. 11) is not formalized. The hypothesis $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 23, §7.1, sentence after (98b)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- p. 23: `K_rtdet` is a proper cone (closed, convex, a cone, pointed, solid). -/
theorem krtdet_proper {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    IsProperCone (Krtdet J) := by sorry

end EJASpectral.RootDet
