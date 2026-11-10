-- Prove2me | Theorems.Thm_CoRSuccGap_proposition_3_3
-- name    : CoRSuccGap.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:20.554604+00:00
-- url     : https://prove2.me/theorems/005520b4-6b4b-43aa-87ca-1fb58f103d7d
-- title:
--   Proposition 3.3 — prediction commutes with $\cup$, $\cap$, complement and converse, and fixes $\mathbf 0,\mathbf 1,\mathbf{id}$
-- statement:
--   Let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with palette $2^{[k]}$ and the two-witness property, let $\hbar$ be the hub and $\lambda$ a colour. For colour-determined relations $X,Y$,
--
--   $$
--   (X\cup Y)^{(\lambda)}=X^{(\lambda)}\cup Y^{(\lambda)},\qquad (X\cap Y)^{(\lambda)}=X^{(\lambda)}\cap Y^{(\lambda)},
--   $$
--   $$
--   \big(\overline X\big)^{(\lambda)}=\overline{X^{(\lambda)}},\qquad (X^{\smile})^{(\lambda)}=\big(X^{(\lambda)}\big)^{\smile},
--   $$
--
--   and the constants $\mathbf 0,\mathbf 1,\mathbf{id}$ are their own predictions.
--
--   Hence among the CoR operations only composition can notice a fold.
--
--   **Formalization Note** The colour $\lambda$ is `lam`; each equation is an equality of relations `V → V → Prop`.
--
--   Differences from the source:
--   - generalization: the standing setting of §3.1: a vertex set of size n ≥ n₀(N) carrying a coloring as in Lemma 3.1, palette of N ≥ 2 colors, palette 2^[k] with k ≥ 1 → any vertex type V and any colouring χ with the two-witness property; reason: the paper fixes such a coloring and its proofs use only the two-witness property; every coloring given by Lemma 3.1 satisfies the hypothesis, so the Lean statement specializes to the source's
--   - generalization: palette 2^[k] for some k ≥ 1 → palette Finset (Fin k) for every k ∈ ℕ; reason: the statement does not need k ≥ 1; for k ≥ 1 it is the source's
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Proposition 3.3, p.20 (PDF 22)

import Mathlib
import Definitions.Def_CoRSuccGap_TwoWitness
import Definitions.Def_CoRSuccGap_ColorDet
import Definitions.Def_CoRSuccGap_predict

set_option autoImplicit false

namespace CoRSuccGap

/-- **Proposition 3.3 (Commutation with prediction).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Proposition 3.3,
p.20 (PDF 22): "For any color λ and color-determined relations X, Y, prediction commutes with
Boolean operations and converse: (X ∪ Y)^(λ) = X^(λ) ∪ Y^(λ), (X ∩ Y)^(λ) = X^(λ) ∩ Y^(λ),
(X̄)^(λ) = \overline{X^(λ)}, (X⌣)^(λ) = (X^(λ))⌣. The constants 0, 1, id are also fixed by
prediction." Standing assumptions: χ is two-witness with hub `h` (§3.1), palette 2^[k] (p.19).

**Formalization Note.** The palette 2^[k] is `Finset (Fin k)`; the colour λ is `lam`. The
two-witness property replaces the standing size n ≥ n₀(2^k); the standing `k ≥ 1` is not needed
and not assumed. -/
theorem proposition_3_3 {V : Type*} [DecidableEq V] {k : ℕ} (χ : Sym2 V → Finset (Fin k))
    (hχ : TwoWitness χ) (h : V) (lam : Finset (Fin k)) (X Y : V → V → Prop)
    (hX : ColorDet χ X) (hY : ColorDet χ Y) :
    predict χ h lam (fun a b => X a b ∨ Y a b) =
        (fun a b => predict χ h lam X a b ∨ predict χ h lam Y a b) ∧
    predict χ h lam (fun a b => X a b ∧ Y a b) =
        (fun a b => predict χ h lam X a b ∧ predict χ h lam Y a b) ∧
    predict χ h lam (fun a b => ¬ X a b) = (fun a b => ¬ predict χ h lam X a b) ∧
    predict χ h lam (fun a b => X b a) = (fun a b => predict χ h lam X b a) ∧
    predict χ h lam (fun _ _ => False) = (fun _ _ => False) ∧
    predict χ h lam (fun _ _ => True) = (fun _ _ => True) ∧
    predict χ h lam (fun a b => a = b) = (fun a b => a = b) := by sorry

end CoRSuccGap
