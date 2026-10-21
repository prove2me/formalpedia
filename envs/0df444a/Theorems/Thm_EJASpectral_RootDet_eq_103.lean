-- Prove2me | Theorems.Thm_EJASpectral_RootDet_eq_103
-- name    : EJASpectral.RootDet.eq_103
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:08.132292+00:00
-- url     : https://prove2.me/theorems/b4a5ad85-cd98-4f42-92a8-5ab50caf7b50
-- title:
--   (103), pp. 24–25 — ∇³ζ(ũ)[p̃,p̃,p̃] ≤ −3(∇²Ψ(ũ)[p̃,p̃])^{1/2} ∇²ζ(ũ)[p̃,p̃] on int(K_rtdet)
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$, $\zeta(u,w) = \det(w)^{1/d} - u$ and $\Psi(u,w) = -\log\det(w)$. For every $\tilde u\in\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$ and every direction $\tilde p = (p,r)\in\mathbb R\times V$,
--   $$\nabla^3\zeta(\tilde u)[\tilde p,\tilde p,\tilde p] \le -3\big(\nabla^2\Psi(\tilde u)[\tilde p,\tilde p]\big)^{1/2}\,\nabla^2\zeta(\tilde u)[\tilde p,\tilde p]. \tag{103}$$
--
--   This is condition (iii) of the compatibility of $\zeta$ with the barrier $\Psi$ in the sense of Nesterov and Nemirovskii (Definition 5.1.2), the heart of the proof of Proposition 7.1.
--
--   **Formalization Note** $(\cdot)^{1/2}$ is the real square root; its argument $\nabla^2\Psi(\tilde u)[\tilde p,\tilde p]$ is nonnegative (by (105)), so this agrees with the paper's power. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, (103); p. 25, "Thus (103) holds"

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- (103), pp. 24–25 ("Thus (103) holds"): for every `ũ ∈ int K_rtdet` and `p̃ ∈ ℝ × V`,
`∇³ζ(ũ)[p̃, p̃, p̃] ≤ −3 (∇²Ψ(ũ)[p̃, p̃])^{1/2} ∇²ζ(ũ)[p̃, p̃]`. -/
theorem eq_103 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    ∀ x ∈ interior (Krtdet J), ∀ h : ℝ × V,
      iteratedFDeriv ℝ 3 (zeta J) x (fun _ => h) ≤
        -3 * Real.sqrt (iteratedFDeriv ℝ 2 (Psi J) x (fun _ => h)) *
          iteratedFDeriv ℝ 2 (zeta J) x (fun _ => h) := by sorry

end EJASpectral.RootDet
