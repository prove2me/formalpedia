-- Prove2me | Theorems.Thm_AsymSpecConn_theorem_2_10
-- name    : AsymSpecConn.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:08.07494+00:00
-- url     : https://prove2.me/theorems/077c1caa-b800-4cf5-bab8-f70fe15042a2
-- title:
--   Theorem 2.10 — interpolation $t\mapsto F_t$ is a path of spectral points
-- statement:
--   Let $\mathcal S$ be a Strassen semiring that is $\mathcal A$-decomposable and let $f_1\in\Delta$. For every $f_0\in\Delta$ such that the pair $f_0,f_1$ has the $\mathcal A$-cover property:
--
--   1. $F_t\in\Delta$ for every $t\in[0,1]$;
--   2. $F_0=f_0$;
--   3. $F_1=f_1$;
--   4. $F_t(a)=f_0(a)^{1-t}f_1(a)^t$ for every $t\in[0,1]$ and $a\in\mathcal A$;
--   5. the map $[0,1]\to\Delta$, $t\mapsto F_t$, is continuous.
--
--   If for every $f_0\in\Delta$ the pair $f_0,f_1$ has the $\mathcal A$-cover property, then moreover:
--
--   6. the map $\Delta\times[0,1]\to\Delta$, $(f_0,t)\mapsto F_t^{f_0}$, is continuous.
--
--   This is the interpolation theorem of the source, and its other results on connectedness follow from it.
--
--   Differences from the source:
--
--   - encoding: F_t ∈ Δ for t ∈ [0,1], and the maps t ↦ F_t and (f_0,t) ↦ F_t^{f_0} → maps Φ : unitInterval → Δ and H : Δ × unitInterval → Δ whose values, coerced to [0,∞], are those of interp; reason: a Lean element of Δ has values in ℝ≥0, and such maps are unique
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Theorem 2.10, p.18

import Mathlib
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_IsADecomposable
import Definitions.Def_AsymSpecConn_HasACoverProperty
import Definitions.Def_AsymSpecConn_interp

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn

/-- **Theorem 2.10** (p.18 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Suppose S is A-decomposable, and let
f1 ∈ ∆. For every f0 ∈ ∆ such that the pair f0, f1 has the A-cover property, the following hold.
(i) Ft ∈ ∆ for every t ∈ [0, 1]. (ii) F0 = f0. (iii) F1 = f1. (iv) For every t ∈ [0, 1] and a ∈ A,
we have Ft(a) = f0(a)^{1−t} f1(a)^t. (v) The map [0, 1] → ∆ : t ↦ Ft is continuous. If for every
f0 ∈ ∆ the pair f0, f1 has the A-cover property, then moreover the following holds. (vi) The map
∆ × [0, 1] → ∆ : (f0, t) ↦ Ft^{f0} is continuous."

**Formalization Note** `F_t = interp P A f₀ f₁ t` (valued in `[0, ∞]`). (i) is the existence of a
map `Φ : [0, 1] → Δ` with `Φ t = F_t` pointwise; such a `Φ` is unique, so (ii)–(v) are stated for
it. Likewise (vi) is the existence of `H : Δ × [0, 1] → Δ` with `H (f₀, t) = F_t^{f₀}` that is
continuous. `[0, 1]` is `unitInterval`; `Δ` carries the topology of pointwise convergence.
`S` is a Strassen semiring (standing assumption of §2, p.12). -/
theorem theorem_2_10 {S : Type*} [CommSemiring S] (P : Preorder S)
    (hS : IsStrassenSemiring S P) (A : Set S) (hA : IsADecomposable P A)
    (f₁ : ↥(Spectrum S P)) :
    (∀ f₀ : ↥(Spectrum S P), HasACoverProperty P A ![f₀, f₁] →
      ∃ Φ : unitInterval → ↥(Spectrum S P),
        (∀ (t : unitInterval) (s : S), (((Φ t).1 s : ℝ≥0) : ℝ≥0∞) = interp P A f₀ f₁ t s) ∧
        Φ 0 = f₀ ∧ Φ 1 = f₁ ∧
        (∀ (t : unitInterval), ∀ a ∈ A,
          (Φ t).1 a = (f₀.1 a) ^ (1 - (t : ℝ)) * (f₁.1 a) ^ (t : ℝ)) ∧
        Continuous Φ) ∧
    ((∀ f₀ : ↥(Spectrum S P), HasACoverProperty P A ![f₀, f₁]) →
      ∃ H : ↥(Spectrum S P) × unitInterval → ↥(Spectrum S P),
        (∀ (f : ↥(Spectrum S P)) (t : unitInterval) (s : S),
          (((H (f, t)).1 s : ℝ≥0) : ℝ≥0∞) = interp P A f f₁ t s) ∧
        Continuous H) := by sorry

end AsymSpecConn
