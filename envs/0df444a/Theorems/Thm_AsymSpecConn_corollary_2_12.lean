-- Prove2me | Theorems.Thm_AsymSpecConn_corollary_2_12
-- name    : AsymSpecConn.corollary_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:03.444955+00:00
-- url     : https://prove2.me/theorems/59588d8d-bc6a-4970-abd6-d5299bcc5144
-- title:
--   Corollary 2.12 — the interpolation homotopy makes $\Delta$ contractible
-- statement:
--   Let $\mathcal S$ be a Strassen semiring that is $\mathcal A$-decomposable, let $f_1\in\Delta$, and suppose that for every $f_0\in\Delta$ the pair $f_0,f_1$ has the $\mathcal A$-cover property. Then
--   $$H:\Delta\times[0,1]\to\Delta,\qquad(f,t)\mapsto F_t^f$$
--   is continuous. It satisfies $H(f,0)=f$ and $H(f,1)=f_1$ for every $f\in\Delta$, and $H(f_1,t)=f_1$ for every $t\in[0,1]$. In particular $\Delta$ is contractible.
--
--   This is the abstract statement from which the contractibility clause of the main theorem follows.
--
--   Differences from the source:
--
--   - encoding: H with H(f,t) = F_t^f → ∃ H : Δ × unitInterval → Δ whose values, coerced to [0,∞], are those of interp; reason: a Lean element of Δ has values in ℝ≥0, and such an H is unique
--   - encoding: contractible, in the sense of p.19 → Mathlib's ContractibleSpace; reason: equivalent: Mathlib's definition is that the identity is nullhomotopic
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Corollary 2.12, p.19

import Mathlib
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_IsADecomposable
import Definitions.Def_AsymSpecConn_HasACoverProperty
import Definitions.Def_AsymSpecConn_interp

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn

/-- **Corollary 2.12** (p.19 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Fix f1 ∈ ∆. Suppose S is
A-decomposable and that for every f0 ∈ ∆ the pair f0, f1 has the A-cover property. Then
H : ∆ × [0, 1] → ∆ : (f, t) ↦ Ft^f is continuous. It satisfies H(f, 0) = f and H(f, 1) = f1 for
every f ∈ ∆, and H(f1, t) = f1 for every t ∈ [0, 1]. In particular ∆ is contractible."

**Formalization Note** `H (f, t) = F_t^f` is `interp P A f f₁ t`; the map `H` is asserted to exist
with these values (it is then unique). "Contractible" (p.19: a point `c` and a continuous
`H : X × [0, 1] → X` with `H(x, 0) = x`, `H(x, 1) = c`) is Mathlib's `ContractibleSpace`
(equivalent, `contractible_iff_id_nullhomotopic`). `S` is a Strassen semiring (standing
assumption of §2, p.12). -/
theorem corollary_2_12 {S : Type*} [CommSemiring S] (P : Preorder S)
    (hS : IsStrassenSemiring S P) (A : Set S) (hA : IsADecomposable P A)
    (f₁ : ↥(Spectrum S P)) (hcov : ∀ f₀ : ↥(Spectrum S P), HasACoverProperty P A ![f₀, f₁]) :
    ∃ H : ↥(Spectrum S P) × unitInterval → ↥(Spectrum S P),
      (∀ (f : ↥(Spectrum S P)) (t : unitInterval) (s : S),
        (((H (f, t)).1 s : ℝ≥0) : ℝ≥0∞) = interp P A f f₁ t s) ∧
      Continuous H ∧
      (∀ f, H (f, 0) = f) ∧ (∀ f, H (f, 1) = f₁) ∧ (∀ t, H (f₁, t) = f₁) ∧
      ContractibleSpace ↥(Spectrum S P) := by sorry

end AsymSpecConn
