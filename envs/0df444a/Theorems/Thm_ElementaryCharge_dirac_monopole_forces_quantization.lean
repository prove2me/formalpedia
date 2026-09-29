-- Prove2me | Theorems.Thm_ElementaryCharge_dirac_monopole_forces_quantization
-- name    : ElementaryCharge.dirac_monopole_forces_quantization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:13:17.347063+00:00
-- url     : https://prove2.me/theorems/e67be5c1-4755-4274-8046-85d2442833fc
-- title:
--   Dirac: a magnetic monopole forces charge quantization
-- statement:
--   Dirac's 1931 argument, in its algebraic form. Suppose a magnetic monopole of nonzero magnetic charge $g$ exists, and that every electric charge $q$ in a collection $Q$ satisfies Dirac's quantization condition $qg = n\hbar/2$ for some integer $n$ depending on $q$. Then every charge in $Q$ is an integer multiple of the single fixed quantum $\hbar/(2g)$: the charge spectrum is quantized. The physical derivation of the condition is outside the statement; what is asserted is that the condition forces quantization.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem dirac_monopole_forces_quantization (Q : Set ℝ) (g hbar : ℝ) (hg : g ≠ 0)
    (hdirac : ∀ q ∈ Q, ∃ n : ℤ, q * g = n * (hbar / 2)) :
    ∀ q ∈ Q, ∃ n : ℤ, q = n * (hbar / (2 * g)) := by sorry

end ElementaryCharge
