-- Prove2me | Theorems.Thm_EJASpectral_RootDet_zeta_concave_smooth
-- name    : EJASpectral.RootDet.zeta_concave_smooth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:19.848766+00:00
-- url     : https://prove2.me/theorems/054c9133-18bc-4c51-9544-a29da35181c1
-- title:
--   Proof of Proposition 7.1, p. 24 — ζ(u, w) = φ(w) − u is concave and C³-smooth on int(E)
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$, $\mathcal E = \mathbb R\times\mathcal Q$, and $\zeta(u,w) = \det(w)^{1/d} - u$ (97). Then $\zeta$ is concave on $\operatorname{int}(\mathcal E)$ and $C^3$-smooth on $\operatorname{int}(\mathcal E)$.
--
--   These are conditions (i) and (ii) of the compatibility criterion used in the proof of Proposition 7.1.
--
--   **Formalization Note** $\operatorname{int}(\mathcal E) = \mathbb R\times\operatorname{int}(\mathcal Q)$. "Concave with respect to $\mathbb R_\ge$" for a real-valued function is ordinary concavity. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, sentence after (104)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- Proof of Proposition 7.1, p. 24: `ζ(u, w) = φ(w) − u` is concave and `C³` on `int E`. -/
theorem zeta_concave_smooth {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    ConcaveOn ℝ (interior (E J)) (zeta J) ∧ ContDiffOn ℝ 3 (zeta J) (interior (E J)) := by sorry

end EJASpectral.RootDet
