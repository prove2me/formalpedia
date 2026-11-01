-- Prove2me | Theorems.Thm_AccessibleMaps_omega_isDensity
-- name    : AccessibleMaps.omega_isDensity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:01:39.446332+00:00
-- url     : https://prove2.me/theorems/174b43d0-bdf8-42a7-bec4-6fb0e1691e62
-- title:
--   Marginal of a density operator: $\operatorname{tr}_A\tau_{AB}$ is a density operator
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and let $\tau$ be a density operator on $\mathbb C^{a}\otimes\mathcal H$ (positive, trace class, trace one). Then its marginal on the environment,
--   $$
--   \omega=\operatorname{tr}_A\tau ,
--   $$
--   is a density operator on $\mathcal H$.
--
--   The paper uses this when it speaks of "the reduced density operator $\omega=\operatorname{tr}_A\tau_{AB}$"; it is what makes $\rho\otimes\omega(\rho)$, and with it the trace-preserving CP part of an accessible map, well defined.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - encoding: ω = tr_A τ_AB on H_A ⊗ H_B → trA τ = Σ_i τ_ii on the block space PiLp 2 (fun _ : a => H); reason: the block space is isometric to C^a ⊗ H
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1

import Mathlib
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_AccessibleMaps_trA

open HayashiHoeffding

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The marginal `ω = tr_A τ_AB` of a density operator on the composite space is a density operator
on `H`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1).

**Formalization Note.** `H` is any complex Hilbert space. -/
theorem omega_isDensity (τ : Composite a H →L[ℂ] Composite a H) (hτ : IsDensityOp τ) :
    IsDensityOp (trA τ) := by sorry

end AccessibleMaps
