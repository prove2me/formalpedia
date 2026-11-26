-- Prove2me | Theorems.Thm_Arxiv2205_09423_transfer_matrix_cascade
-- name    : Arxiv2205_09423.transfer_matrix_cascade
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T12:42:17.013874+00:00
-- url     : https://prove2.me/theorems/c307e176-d25c-575f-b21b-eda715c38cdf
-- title:
--   Eqs. (C2)–(C3): transfer matrix of a stack of layers
-- statement:
--   Let the mode set be as in Section 2.1, and let $N\ge1$ layers be given, layer $l$ consisting of particles that lie in a slab of thickness $\Delta L_l>0$ centred at the origin. Let $\bar{\mathbf M}^0_l$ be the transfer matrix of layer $l$ at the origin, assuming its $\bar{\mathbf t}'$ block is invertible. Let $\bar{\mathbf M}^{L_l}_l$ be the transfer matrix of the same layer translated to centre $L_l$, with $L_1<\dots<L_N$. Then
--
--   $$\bar{\mathbf M}^{L_N}_N\cdots\bar{\mathbf M}^{L_1}_1=\Lambda_\mp^{L_N}\bar{\mathbf M}^0_N\Lambda_\pm^{L_N-L_{N-1}}\cdots\bar{\mathbf M}^0_2\Lambda_\pm^{L_2-L_1}\bar{\mathbf M}^0_1\Lambda_\pm^{L_1}.$$
--
--   If moreover all layers have the same thickness $\Delta L$ and are contiguous, $L_1=0$ and $L_{l+1}-L_l=\Delta L$, then
--
--   $$\bar{\mathbf M}^{L_N}_N\cdots\bar{\mathbf M}^{L_1}_1=\Lambda_\mp^{N\Delta L}\prod_{l=N}^{1}\Lambda_\pm^{\Delta L}\bar{\mathbf M}^0_l$$
--
--   (product with $l=N$ on the left). For every $L$, left multiplication by $\Lambda_\mp^{L}$ multiplies each $2\times2$ block of a matrix by a single unimodular phase factor.
--
--   So a medium of thickness $N\Delta L$ is obtained by cascading $N$ matrices $\Lambda_\pm^{\Delta L}\bar{\mathbf M}^0$, up to a leading phase that does not alter intensity or polarization statistics.
--
--   **Formalization Note** Layers are indexed by $l=0,\dots,N-1$ in Lean. The general formula is written with the convention $L_0:=0$ for the last factor, which is $\Lambda_\pm^{L_1}$. That the transfer matrix of a stack is the ordered product of the layers' transfer matrices is the premise (quoted from Beenakker); the statement is the identity between that product and the right-hand sides. The "intensity and polarization statistics" remark is stated as the precise block-phase property.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c009; Section 2.3, PDF p. 11, and Appendix C, Eqs. (C2)-(C3), PDF pp. 25-26

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem transfer_matrix_cascade {Nk : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (M : ℕ) (hM : 0 < M)
    (Np : ℕ → ℕ) (A : ∀ l, Fin (Np l) → Amp) (r : ∀ l, Fin (Np l) → Fin 3 → ℝ)
    (dL : ℕ → ℝ) (hdL : ∀ l, 0 < dL l) (hr : ∀ l p, r l p 2 ∈ Set.Icc (-dL l / 2) (dL l / 2))
    (hinv : ∀ l, IsUnit (assemble (tpbar K (A l) (r l))).det)
    (L : ℕ → ℝ) (hL : ∀ l, l + 1 < M → L l < L (l + 1)) :
    let M0 := fun l => transfer (sMat K (A l) (r l))
    let ML := fun l => transfer (sMat K (A l) (shiftZ (L l) (r l)))
    ((List.range M).map ML).reverse.prod =
        lamMP K (L (M - 1)) *
          ((List.range M).map fun l =>
            M0 l * lamPM K (L l - if l = 0 then 0 else L (l - 1))).reverse.prod ∧
    (∀ D : ℝ, (∀ l, dL l = D) → L 0 = 0 → (∀ l, l + 1 < M → L (l + 1) - L l = D) →
      ((List.range M).map ML).reverse.prod =
        lamMP K (M * D) * ((List.range M).map fun l => lamPM K D * M0 l).reverse.prod) ∧
    ∀ L' : ℝ, ∃ ph : Fin (2 * Nk + 1) ⊕ Fin (2 * Nk + 1) → ℂ, (∀ s, ‖ph s‖ = 1) ∧
      ∀ (X : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ) x y,
        (lamMP K L' * X) x y = ph (Sum.map Prod.fst Prod.fst x) * X x y := by sorry

end Arxiv2205_09423
