-- Prove2me | Theorems.Thm_FaulhuberTFA_crossAmbiguity_orthogonality
-- name    : FaulhuberTFA.crossAmbiguity_orthogonality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:52:29.71024+00:00
-- url     : https://prove2.me/theorems/eaa8c9c8-69da-4a7e-b8e5-d570916bee0b
-- title:
--   Orthogonality relations for the cross-ambiguity function
-- statement:
--   Let $f_1,f_2,g_1,g_2\in L^2(\mathbb{R}^d)$. Then
--
--   $$\langle A(f_1,g_1),A(f_2,g_2)\rangle_{L^2(\mathbb{R}^{2d})}=\langle f_1,f_2\rangle\,\overline{\langle g_1,g_2\rangle},$$
--
--   and consequently
--
--   $$\|A(f_1,g_1)\|_{L^2(\mathbb{R}^{2d})}=\|f_1\|_2\,\|g_1\|_2 .$$
--
--   The orthogonality relations of the STFT carry over unchanged to the cross-ambiguity function.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, display after the Remark, p. 30

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem crossAmbiguity_orthogonality {d : ℕ} {f₁ f₂ g₁ g₂ : Rd d → ℂ}
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume) :
    (∫ p : Rd d × Rd d, crossAmbiguity f₁ g₁ p.1 p.2 * starRingEnd ℂ (crossAmbiguity f₂ g₂ p.1 p.2) =
      l2inner f₁ f₂ * starRingEnd ℂ (l2inner g₁ g₂)) ∧
    eLpNorm (fun p : Rd d × Rd d => crossAmbiguity f₁ g₁ p.1 p.2) 2 volume =
      eLpNorm f₁ 2 volume * eLpNorm g₁ 2 volume := by sorry

end FaulhuberTFA
