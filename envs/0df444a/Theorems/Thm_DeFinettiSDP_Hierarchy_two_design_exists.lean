-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_two_design_exists
-- name    : DeFinettiSDP.Hierarchy.two_design_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:49.367983+00:00
-- url     : https://prove2.me/theorems/8b7c9e80-a0a5-4906-8564-ec4f2a6c1336
-- title:
--   App. D, p. 29 (after Lemma D.1) — state two-designs exist in every dimension
-- statement:
--   For every dimension $d\ge1$ there is a state two-design: a finite family of $t\ge1$ rank-one projectors $P_1,\dots,P_t$ on $\mathbb C^d$ such that
--
--   $$\frac1t\sum_{z=1}^tP_z\otimes P_z=\frac{2P^{\mathrm{sym}}}{d(d+1)},$$
--
--   where $P^{\mathrm{sym}}$ is the projector onto the symmetric subspace of $\mathbb C^d\otimes\mathbb C^d$.
--
--   The paper cites this fact ([68, Corollary 5.3] for unitary two-designs, applied to a fixed state); it makes Lemma D.1 applicable in every dimension and so yields $f(B|\cdot)\le d_B^2(d_B+1)$.
--
--   **Formalization Note** The design has equal weights $1/t$, as in Lemma D.1; weighted designs are not allowed.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, App. D, p. 29, the sentence after Lemma D.1 (citing [68, Corollary 5.3])

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Existence of state two-designs** (arXiv:1810.12197v3, App. D, p. 29, the sentence after
Lemma D.1). In every dimension `d ≥ 1` there is a finite family of `t ≥ 1` rank-one projectors
`P_z` with `(1/t) ∑_z P_z ⊗ P_z = 2 P^sym / (d (d+1))` (equal weights). -/
theorem two_design_exists :
    ∀ d : ℕ, 1 ≤ d → ∃ (t : ℕ) (P : Fin t → Matrix (Fin d) (Fin d) ℂ),
      0 < t ∧ IsStateTwoDesign P := by sorry

end DeFinettiSDP.Hierarchy
