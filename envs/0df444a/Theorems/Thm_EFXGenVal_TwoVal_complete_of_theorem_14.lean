-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_complete_of_theorem_14
-- name    : EFXGenVal.TwoVal.complete_of_theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:56.188011+00:00
-- url     : https://prove2.me/theorems/098fe39f-6e24-4562-865e-463847ee9c93
-- title:
--   Section 4, p. 12, sentence after Theorem 14 — the progress step yields a complete EFX allocation
-- statement:
--   Let the agents have normalized, monotone, non-degenerate valuations, with $v_a$ on a nonempty class $N_a$ and $v_b$ on the nonempty class $N_b$. Suppose the conclusion of Theorem 14 holds: for every partial EFX allocation $X$ there is an EFX allocation $Y$ with $Y\succ_{\mathrm{p.lexmin}}X$. Then there exists a complete EFX allocation, i.e. an EFX allocation in which every item is allocated.
--
--   This is the termination step that turns the progress step into Theorem 1 for non-degenerate instances: the strict order $\succ_{\mathrm{p.lexmin}}$ cannot increase forever on the finitely many allocations, and the empty allocation is EFX.
--
--   **Formalization Note** The hypothesis of Theorem 14 is a binder `h14` quantified over all allocations $X$ with a nonempty pool that are EFX. "Complete" is `pool X = ∅`.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, Section 4, p. 12, sentence after Theorem 14

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem complete_of_theorem_14 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (h14 : ∀ X : Fin n → Finset (Fin m), IsPartialAllocation X → (pool X).Nonempty →
      IsEFX v X → ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
        PLexGT va vb A Y X) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ pool X = ∅ ∧ IsEFX v X := by sorry

end EFXGenVal.TwoVal
