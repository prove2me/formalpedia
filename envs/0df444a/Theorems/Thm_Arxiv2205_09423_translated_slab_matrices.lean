-- Prove2me | Theorems.Thm_Arxiv2205_09423_translated_slab_matrices
-- name    : Arxiv2205_09423.translated_slab_matrices
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T12:32:54.157499+00:00
-- url     : https://prove2.me/theorems/3b14a876-b51a-5f24-8da9-0a38c1969a3c
-- title:
--   Eq. (28) and Eq. (C1): scattering and transfer matrices of a translated slab
-- statement:
--   Let the mode set be as in Section 2.1, and let a slab of thickness $\Delta L>0$ centred at $z=0$ contain particles with centres $\mathbf r_p$, $|z_p|\le\Delta L/2$, and amplitude matrices $\mathbf A_p$. Translate every particle by $L_0\hat{\mathbf z}$, and write a superscript $L_0$ for the matrices of the translated slab and $0$ for those of the original one. Then:
--
--   1. $\bar{\mathbf t}^{L_0}_{(j,i)}=\bar{\mathbf t}^{0}_{(j,i)}\exp[i(k_{iz}-k_{jz})L_0]$ for all modes $i,j$, hence $\bar{\mathbf t}^{L_0}=\Lambda_-^{L_0}\bar{\mathbf t}^0\Lambda_+^{L_0}$ with $\Lambda_+^{L_0}=\mathrm{diag}(e^{ik_{-N_kz}L_0},\dots,e^{ik_{N_kz}L_0})\otimes\mathbb I_2$ and $\Lambda_-^{L_0}=(\Lambda_+^{L_0})^*$;
--   2. $\bar{\mathbf S}^{L_0}=\Lambda_\pm^{L_0}\bar{\mathbf S}^0\Lambda_\pm^{L_0}$, with $\Lambda_\pm^{L_0}=\mathrm{diag}(\Lambda_+^{L_0},\Lambda_-^{L_0})$;
--   3. if $\bar{\mathbf t}'^{\,0}$ is invertible, then $\bar{\mathbf M}^{L_0}=\Lambda_\mp^{L_0}\bar{\mathbf M}^0\Lambda_\pm^{L_0}$, with $\Lambda_\mp^{L_0}=(\Lambda_\pm^{L_0})^*$.
--
--   This lets a slab at any position be generated from one at the origin, whose statistics are those of Section 2.2.
--
--   **Formalization Note** The transfer matrix is defined from $\bar{\mathbf S}$ in Beenakker's convention, which the paper cites but does not write out; it requires $\bar{\mathbf t}'$ to be invertible, which is therefore assumed. $\bar{\mathbf t}'$ and $\bar{\mathbf r}'$ are written by analogy with Eqs. (14)–(15).
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c008; Section 2.3, Eq. (28), PDF p. 11, and Appendix C, Eq. (C1), PDF p. 25

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem translated_slab_matrices {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL : ℝ)
    (hdL : 0 < dL) (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ)
    (hr : ∀ p, r p 2 ∈ Set.Icc (-dL / 2) (dL / 2)) (L0 : ℝ) :
    (∀ j i, tbar K A (shiftZ L0 r) j i =
      Complex.exp (Complex.I * (((K.kz i - K.kz j) * L0 : ℝ) : ℂ)) • tbar K A r j i) ∧
    assemble (tbar K A (shiftZ L0 r)) = lamMinus K L0 * assemble (tbar K A r) * lamPlus K L0 ∧
    sMat K A (shiftZ L0 r) = lamPM K L0 * sMat K A r * lamPM K L0 ∧
    (IsUnit (assemble (tpbar K A r)).det →
      transfer (sMat K A (shiftZ L0 r)) = lamMP K L0 * transfer (sMat K A r) * lamPM K L0) := by sorry

end Arxiv2205_09423
