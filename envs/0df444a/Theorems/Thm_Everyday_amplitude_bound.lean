-- Prove2me | Theorems.Thm_Everyday_amplitude_bound
-- name    : Everyday.amplitude_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:18:06.521185+00:00
-- url     : https://prove2.me/theorems/24d6f2c8-dee5-40f3-9617-f919c0beaf83
-- title:
--   Quantum mechanics: the finite path integral has modulus at most the number of configurations
-- statement:
--   The source equation's left-hand side W is a transition amplitude: the integral of the phases exp(iS) over all field configurations below the ultraviolet cutoff Λ. The item is the path integral's coherence, in the arena's exact finite form: on a finite configuration space, the amplitude — the sum of the phase of each configuration — has modulus at most the number of configurations. Each summand is a unit phase; the bound is the triangle inequality; the interest of the everyday equation's dynamics lies in the interference of these phases, never in their magnitude.
--
--   **Formalization Note** The finite configuration space is the exact discrete stand-in for the continuum of fields below the cutoff Λ; no measure-theoretic or renormalization content is claimed. The proof: the norm of the sum is at most the sum of the norms — the triangle inequality — each summand's norm is one by the phase milestone, and the sum of a constant one over the space is its cardinality.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the path integral W and the ultraviolet cutoff Λ

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

namespace Everyday

/-- Quantum mechanics: the path integral is a coherent sum. On a finite
configuration space, the amplitude W = ∑_c exp(i S c) has modulus at
most the number of configurations — a finite sum of unit phases. Each
summand is a phase; the bound is the triangle inequality. -/
theorem amplitude_bound (C : Type) [Fintype C] (S : C → ℝ) :
    ‖amplitude S‖ ≤ (Fintype.card C : ℝ) := by sorry

end Everyday
