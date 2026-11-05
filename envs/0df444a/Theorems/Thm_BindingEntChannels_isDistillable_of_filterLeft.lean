-- Prove2me | Theorems.Thm_BindingEntChannels_isDistillable_of_filterLeft
-- name    : BindingEntChannels.isDistillable_of_filterLeft
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:39.228579+00:00
-- url     : https://prove2.me/theorems/a41c98ed-1de8-48f7-8c47-4246c2c84b44
-- title:
--   §II, p. 2 — the local filter $\Gamma\otimes I$ cannot create free entanglement
-- statement:
--   Let $\Gamma$ be a completely positive map on Alice's side, given by finitely many Kraus operators and not necessarily trace preserving, and let $\tau$ be any operator on $\mathbb C^I\otimes\mathbb C^J$. If $(\Gamma\otimes I)\tau$ is distillable, then $\tau$ is distillable:
--
--   $$
--   (\Gamma\otimes I)\tau\ \text{FE}\ \Longrightarrow\ \tau\ \text{FE}.
--   $$
--
--   Equivalently, $\Gamma\otimes I$ maps a state that is not FE, in particular a BE state, to a state that is not FE.
--
--   Differences from the source:
--   - generalization: Γ ⊗ I cannot produce an FE state from a BE one → if (Γ ⊗ I)τ is distillable then τ is distillable, for every τ; reason: contrapositive with no entanglement hypothesis on τ; at a BE τ it is the paper's sentence
--   - reading: FE (free entanglement) and BE (bound entanglement) → FE = distillable (definition of ref. [3]); BE = density matrix, not separable, not distillable; reason: p. 1: FE "can be converted into pure singlet form", BE "cannot be distilled"; p. 2: a non-BE state "can be separable or FE"
--   - encoding: Γ is CP, but not necessarily trace-preserving → Γ given by a finite Kraus family G with no completeness condition; reason: every CP map between finite-dimensional matrix algebras has a finite Kraus form
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "the action Γ ⊗ I is LQCC one, hence cannot produce FE state from a BE one")

import Mathlib
import Definitions.Def_BindingEntChannels_filterLeft
import Definitions.Def_BoundEntPPT_IsDistillable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): "indeed the action Γ ⊗ I is LQCC one, hence cannot produce FE
state from a BE one".

For every CP map `Γ` (finite Kraus family `G`, not necessarily trace preserving) and every
operator `τ` on `I × J`: if `(Γ ⊗ I)τ` is distillable, then `τ` is distillable.

**Formalization Note.** Contrapositive form, with no hypothesis that `τ` is entangled: if `τ`
is BE (in particular not distillable), then `(Γ ⊗ I)τ` is not distillable, hence not FE. -/
theorem isDistillable_of_filterLeft {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] {r : ℕ} (G : Fin r → Matrix K I ℂ)
    (τ : Matrix (I × J) (I × J) ℂ) (h : BoundEntPPT.IsDistillable (filterLeft G τ)) :
    BoundEntPPT.IsDistillable τ := by sorry

end BindingEntChannels
