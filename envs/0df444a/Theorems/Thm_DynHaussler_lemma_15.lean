-- Prove2me | Theorems.Thm_DynHaussler_lemma_15
-- name    : DynHaussler.lemma_15
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:35:55.045208+00:00
-- url     : https://prove2.me/theorems/0e557e98-d3a8-41b3-870b-e11f7d41e6ec
-- title:
--   Lemma 15 — $\mathrm{Ldim}(A^{\pm})\le\mathrm{sfat}_\eta(H)$ for the partial error classes
-- statement:
--   Let $\eta>0$ and $H\subseteq[0,1]^X$, and let $A^{\pm}=\{\phi^{\pm}_f:f\in H\}$ be the partial error classes of Eq. (39). Then
--   $$
--   \mathrm{Ldim}(A^+),\ \mathrm{Ldim}(A^-)\le\mathrm{sfat}_\eta(H). \tag{40}
--   $$
--
--   The lemma transfers the sequential fat-shattering bound to the partial binary classes that encode one-sided prediction errors, so that Lemmas 16 and 17 apply to them.
--
--   **Formalization Note** The statement treats one class at a time through a sign flag.
--
--   Differences from the source:
--   - generalization: H is the fixed nonempty separated class of Section 4, with 0 < η < 1 → every H ⊆ [0,1]^X and every η > 0; reason: the proof uses neither separation, nonemptiness nor η < 1; the source's H is an instance
--   - generalization: A^± defined on Z = X × [0,1] → A^± defined on X × ℝ by the same formula; reason: restricting to X × [0,1] can only lower the Littlestone dimension, so the bound on X × ℝ implies the source's
--   - encoding: Ldim with −1 for the empty class → partialLdim in ℕ∞ with 0 for the empty class; reason: for H = ∅ both sides are 0 in Lean and −1 in the source; the inequality holds in both
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 15, Eq. (40), p.22 (PDF p.24); classes (39), p.22

import Mathlib
import Definitions.Def_DynHaussler_errClass
import Definitions.Def_DynHaussler_partialLdim
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 15 (Dimension of the partial error classes).** Both partial classes `A^± = {ϕ^±_f : f ∈ H}`
of Eq. (39) satisfy `Ldim(A^+), Ldim(A^−) ≤ sfat_η(H)` (Eq. (40)).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 15, Eq. (40), p.22 (PDF p.24); the classes (39), p.22.

**Formalization Note** In the paper `H` is the fixed nonempty separated class of Section 4 with
`0 < η < 1`; the statement here holds for every `H ⊆ [0,1]^X` and `η > 0`, and the partial classes
are defined on `X × ℝ` rather than `X × [0,1]`. The value `plus = true` is `A^+`, `false` is `A^−`. -/
theorem lemma_15 {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (H : Set (X → ℝ))
    (hH01 : ∀ f ∈ H, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (plus : Bool) :
    partialLdim (errClass η H plus) ≤ NondualOpt.sfat H η := by sorry

end DynHaussler
