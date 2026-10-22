-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_regularization_identity
-- name    : BirkhoffGlobalSection.leviCivita_regularization_identity
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:07:21.034673+00:00
-- url     : https://prove2.me/theorems/f78e2348-f68e-4b87-b82d-886138708fc5
-- title:
--   Equation 2.2 — Levi-Civita regularization identity
-- statement:
--   Let $s=(z_1,z_2,w_1,w_2)$ satisfy both $|z|^2>0$ and $D(z)>0$. Thus neither the regularized collision at the chosen primary nor the remaining singular collision is present. Under the inverse Levi-Civita coordinate change $q+\mu=2z^2$ and $p=w/\bar z$, the regularized and unregularized Hamiltonians satisfy
--
--   $$
--   K_{\mu,c}(s)=|z|^2\bigl(H_\mu(q,p)+c\bigr).
--   $$
--
--   This is the scalar algebraic identity underlying Joung--van Koert equation (2.2). On $K_{\mu,c}=0$ it identifies the corresponding Jacobi energy as $H_\mu=-c$; the vector-field identity and positive time reparametrization are separate dynamical statements.
-- source:
--   Joung--van Koert, equation (2.2) and the immediately following scalar/vector-field relation, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Equation (2.2): away from both collision loci, the Levi-Civita Hamiltonian
is the shifted Jacobi Hamiltonian multiplied by `|z|²`. -/
theorem leviCivita_regularization_identity (μ c : ℝ) (s : Phase)
    (hz : 0 < zNormSq s) (hD : 0 < secondCollisionDistanceSq s) :
    leviCivitaHamiltonian μ c s =
      zNormSq s * (jacobiHamiltonian μ (leviCivitaToJacobi μ s) + c) := by sorry

end BirkhoffGlobalSection
