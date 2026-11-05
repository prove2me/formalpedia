-- Prove2me | Theorems.Thm_BindingEntChannels_isSeparable_filterLeft
-- name    : BindingEntChannels.isSeparable_filterLeft
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:32.667431+00:00
-- url     : https://prove2.me/theorems/8634d63d-802a-4895-8c97-5ac65e5fcd5f
-- title:
--   §II, p. 2 — a local filter $\Gamma\otimes I$ maps separable states to separable states
-- statement:
--   Let $\tau$ be a separable state on $\mathbb C^I\otimes\mathbb C^J$ and let $\Gamma$ be a completely positive map on Alice's side, given by finitely many Kraus operators and not necessarily trace preserving, such that $\operatorname{Tr}\,(\Gamma\otimes I)\tau>0$. Then the normalized state
--
--   $$
--   \frac{(\Gamma\otimes I)\tau}{\operatorname{Tr}\,(\Gamma\otimes I)\tau}
--   $$
--
--   is separable; in particular it is not bound entangled.
--
--   **Formalization Note** The positive trace (the filter succeeds with positive probability) excludes the junk value of dividing by zero.
--
--   Differences from the source:
--   - reading: LQCC action → the local filter Γ ⊗ I; reason: the sentence is the parenthetical justification of "since Γ ⊗ I is LQCC"; the protocol-level statement is the milestone for the separable case
--   - generalization: cannot make a BE state from a separable one → the normalized output is separable; reason: separable states are not BE, so this implies the sentence
--   - encoding: Γ is CP, but not necessarily trace-preserving → Γ given by a finite Kraus family G with no completeness condition; reason: every CP map between finite-dimensional matrix algebras has a finite Kraus form
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "LQCC action cannot make BE state from separable one")

import Mathlib
import Definitions.Def_BindingEntChannels_filterLeft
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem, necessity): "LQCC action cannot make BE state from separable
one", for the action `Γ ⊗ I` used there.

For a separable state `τ` on `I × J` and a CP map `Γ` (finite Kraus family `G`, not
necessarily trace preserving) such that `(Γ ⊗ I)τ` has positive trace (the filter succeeds with
positive probability), the normalized state `(Γ ⊗ I)τ / Tr((Γ ⊗ I)τ)` is separable.

**Formalization Note.** The conclusion "separable" excludes "BE" and is the stronger form. The
positive-trace hypothesis excludes the junk value `0⁻¹ = 0` of the normalization. -/
theorem isSeparable_filterLeft {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [Fintype K] {r : ℕ} (G : Fin r → Matrix K I ℂ) (τ : Matrix (I × J) (I × J) ℂ)
    (hτ : HorodeckiBoundKey.IsSeparable τ) (hpos : 0 < (filterLeft G τ).trace.re) :
    HorodeckiBoundKey.IsSeparable (((filterLeft G τ).trace)⁻¹ • filterLeft G τ) := by sorry

end BindingEntChannels
