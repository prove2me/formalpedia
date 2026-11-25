-- Prove2me | Theorems.Thm_Arxiv2602_07094_pauli_sq_moduli_formula
-- name    : Arxiv2602_07094.pauli_sq_moduli_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:38:30.037481+00:00
-- url     : https://prove2.me/theorems/dbbfd671-14e2-472a-a6fd-a6ec8ac7e60e
-- title:
--   Section 3.1, from eq. (4) and the coefficient formulas below it: squared moduli of the Pauli coefficients alpha and beta (derived; not printed in the paper)
-- statement:
--   Let $\mathbf S$ be a reciprocal Sinclair matrix with Pauli coefficients $\alpha=(S_{hh}+S_{vv})/\sqrt2$ and $\beta=(S_{hh}-S_{vv})/\sqrt2$. Then
--
--   $$|\alpha|^2=\tfrac12\big(|S_{hh}|^2+|S_{vv}|^2+2\,\mathrm{Re}(S_{hh}\overline{S_{vv}})\big),\qquad |\beta|^2=\tfrac12\big(|S_{hh}|^2+|S_{vv}|^2-2\,\mathrm{Re}(S_{hh}\overline{S_{vv}})\big).$$
--
--   The two moduli shown in the Pauli RGB image therefore depend on the relative phase of $S_{hh}$ and $S_{vv}$ through $\mathrm{Re}(S_{hh}\overline{S_{vv}})$, and not only on the channel amplitudes.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), claim c024; Section 3.1, eq. (4) and the coefficient formulas below it, PDF p. 4; used in Section 4, opening paragraph, PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

open Matrix

namespace Arxiv2602_07094

theorem pauli_sq_moduli_formula (S : SinclairMatrix) (hS : IsReciprocal S) :
    ‖pauliAlpha S‖ ^ 2 = (‖S 0 0‖ ^ 2 + ‖S 1 1‖ ^ 2 + 2 * (S 0 0 * star (S 1 1)).re) / 2 ∧
    ‖pauliBeta S‖ ^ 2 = (‖S 0 0‖ ^ 2 + ‖S 1 1‖ ^ 2 - 2 * (S 0 0 * star (S 1 1)).re) / 2 := by sorry

end Arxiv2602_07094
