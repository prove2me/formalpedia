-- Prove2me | Theorems.Thm_EJASpectral_RootDet_psi_lhscb
-- name    : EJASpectral.RootDet.psi_lhscb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:55.89447+00:00
-- url     : https://prove2.me/theorems/ce02d4b5-dff8-40fa-95b8-90777c25af34
-- title:
--   Proof of Proposition 7.1, p. 24 — Ψ(u, w) = −logdet(w) is a d-LHSCB for E = ℝ × Q
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$, and let $\mathcal E = \mathbb R\times\mathcal Q$. Then
--   $$\Psi(u,w) := -\log\det(w)$$
--   is a **$d$-logarithmically homogeneous self-concordant barrier** for $\mathcal E$: it is $C^3$ and convex on $\operatorname{int}(\mathcal E)$, tends to $+\infty$ at the boundary of $\mathcal E$ from inside, satisfies $\Psi(\theta\tilde u) = \Psi(\tilde u) - d\log\theta$ for $\theta>0$, and satisfies the self-concordance inequality (39).
--
--   This is the classical fact that $-\log\det$ is the standard barrier of a symmetric cone with parameter equal to the rank (recalled on p. 12); it is the barrier with which $\zeta$ is shown compatible in the proof of Proposition 7.1.
--
--   **Formalization Note** $\mathcal E$ is not pointed, so properness is not claimed. $\Psi$ does not depend on $u$, so its Hessian is degenerate in the $u$ direction; the definition of LHSCB used here does not require nondegeneracy. $d\ge1$ is added because the paper divides by $d$ and requires $\nu\ge1$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, first sentence; recalled on p. 12

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- Proof of Proposition 7.1, p. 24: `Ψ(u, w) = −logdet(w)` is a `d`-LHSCB for `E = ℝ × Q`. -/
theorem psi_lhscb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    IsLHSCB (E J) (Psi J) (d : ℝ) := by sorry

end EJASpectral.RootDet
