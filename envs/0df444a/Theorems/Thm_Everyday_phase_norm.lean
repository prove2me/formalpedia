-- Prove2me | Theorems.Thm_Everyday_phase_norm
-- name    : Everyday.phase_norm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:17:27.200411+00:00
-- url     : https://prove2.me/theorems/62560843-ce70-4a91-bb59-4191fb0338d2
-- title:
--   Quantum mechanics: the exponential of i times a real action is a unit phase
-- statement:
--   The image's first label is quantum mechanics itself: the source equation's dynamics enters through the exponential of i times the action — the phase of each configuration in the path integral. The item is the phase's unitarity: for a real number s — the action of a configuration, in the image's units where ℏ = 1 — the complex number exp(i s) has modulus exactly one. A phase contributes direction, never magnitude.
--
--   **Formalization Note** The action is dimensionless with ℏ = 1, the units of the image, so the phase is exp(iS) rather than exp(iS/ℏ). The proof: the modulus of the complex exponential is the real exponential of the real part of its argument, and the real part of i times a real coercion is zero, so the modulus is the exponential of zero, which is one.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the quantum-mechanics label exp{i∫…}

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

namespace Everyday

/-- Quantum mechanics: the exponential of i times a real number is a
phase — the amplitude exp(iS) contributed by a single configuration of
real action S has modulus exactly one. -/
theorem phase_norm (s : ℝ) : ‖Complex.exp (Complex.I * (s : ℂ))‖ = 1 := by sorry

end Everyday
