-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_lemma_D_1
-- name    : DeFinettiSDP.Hierarchy.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:47.884978+00:00
-- url     : https://prove2.me/theorems/98c7e998-5580-4804-a96a-ecfd7d6fab26
-- title:
--   Lemma D.1, p. 29 — the two-design measurement satisfies ‖(I_A ⊗ M_B)(ξ)‖₁ ≥ ‖ξ‖₁/(d_B²(d_B+1)) for every Hermitian ξ
-- statement:
--   Let $\{P_z\}_{z=1}^t$, $t\ge1$, be a state two-design on a $d_B$-dimensional system $B$: rank-one projectors with $\frac1t\sum_zP_z\otimes P_z=2P^{\mathrm{sym}}/(d_B(d_B+1))$. Let $\mathcal M_B(X)=\sum_z\frac{d_B}{t}\mathrm{Tr}[P_zX]\,|z\rangle\langle z|$. Then for every finite-dimensional system $A$ and every Hermitian matrix $\xi_{AB}$ on $A\otimes B$,
--
--   $$\big\|(\mathcal I_A\otimes\mathcal M_B)(\xi_{AB})\big\|_1\ \ge\ \frac{1}{d_B^2(d_B+1)}\,\|\xi_{AB}\|_1.$$
--
--   The bound does not depend on $d_A$: measuring $B$ with a two-design loses at most a factor $d_B^2(d_B+1)$ of trace-norm distinguishability, whatever side system is kept. It gives the bound $f(B|\cdot)\le d_B^2(d_B+1)$.
--
--   **Formalization Note** $(\mathcal I_A\otimes\mathcal M_B)(\xi)$ is the block-diagonal operator on $A\otimes Z$ with blocks $\frac{d_B}{t}\mathrm{Tr}_B[(\mathbb 1_A\otimes P_z)\xi]$. The inequality is stated with the division on the left, $\|\xi\|_1/(d_B^2(d_B+1))\le\|(\mathcal I_A\otimes\mathcal M_B)(\xi)\|_1$, and for every dimension $d_A$. The hypothesis $t\ge1$ makes $\frac1t$ meaningful.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, App. D, Lemma D.1, p. 29

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Lemma D.1** (arXiv:1810.12197v3, p. 29). Let `{P_z}_{z=1}^t` (`t ≥ 1`) be a state two-design
on a `d_B`-dimensional system `B`, and `M_B` the measurement with effects `(d_B/t) P_z`. For every
finite-dimensional system `A` and every Hermitian `ξ` on `A ⊗ B`,
`‖(I_A ⊗ M_B)(ξ)‖₁ ≥ ‖ξ‖₁ / (d_B² (d_B + 1))`. -/
theorem lemma_D_1 {dB t : ℕ} (P : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (ht : 0 < t)
    (hP : IsStateTwoDesign P) :
    ∀ (dA : ℕ) (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ), ξ.IsHermitian →
      WildeQIT.traceNorm ξ / ((dB : ℝ) ^ 2 * ((dB : ℝ) + 1)) ≤
        WildeQIT.traceNorm (measB (designMeas P) ξ) := by sorry

end DeFinettiSDP.Hierarchy
