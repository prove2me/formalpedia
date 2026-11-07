-- Prove2me | Theorems.Thm_ContinualCounting_eq_20_signal_lower_bound
-- name    : ContinualCounting.eq_20_signal_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:30.281203+00:00
-- url     : https://prove2.me/theorems/296433f6-2ca9-4059-9951-0c9e4efaff78
-- title:
--   Eq. (20) — the signal is $\Omega(h^2)$
-- statement:
--   Let $4\mid h$, $s\in\{\ell,r\}^{h/2}$, and let $\mathcal J,\{J_d\}$ be a selection. Then
--   $$\sum_{i\in\mathcal L(\mathcal T^s)}\langle\psi^i,\mu^i\rangle^2\ge2^{-8}h^2.$$
--
--   Together with Lemmas 1, 5, 6 this forces one residual noise in the selection to be $\Omega(\sqrt h/\max\{\varepsilon,\delta\})$.
--
--   Differences from the source:
--   - generalization: §5 assumes n is a power of 16 → every h with 4 ∣ h; reason: the computation needs only that h/4 is an integer
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, eq. (20), p.30 (PDF p.31)

import Mathlib
import Definitions.Def_ContinualCounting_psi

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Eq. (20) (the signal is `Ω(h²)`).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…),
§5, p.30: "∑_{i∈L(T^s)} ⟨ψ^i, µ^i⟩^2 ≥ 2^{−8}h^2", for every `s` and every admissible `J, {J_d}`.

**Formalization Note.** Arithmetic on reals. `4 ∣ h` is what makes `h / 4` an integer, as in §5. -/
theorem eq_20_signal_lower_bound {h : ℕ} (hh : 4 ∣ h) (s : Fin (h / 2) → Bool) (J : Finset ℕ)
    (Js : ℕ → Finset Node) (hJ : Admissible h s J Js) :
    (2 : ℝ) ^ (-8 : ℤ) * (h : ℝ) ^ 2 ≤
      ∑ i ∈ leavesTs h s, attackInner h s (psi h i) (mu h s J Js i) ^ 2 := by sorry

end ContinualCounting
