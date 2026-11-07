-- Prove2me | Theorems.Thm_DynBrooks_lemma_5_4
-- name    : DynBrooks.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:26.856891+00:00
-- url     : https://prove2.me/theorems/adbff380-288c-4520-b1da-e330d2201586
-- title:
--   Lemma 5.4 — $W_m\le 12\,\Delta^{(3-m)/512}$ for $\Delta\ge16$
-- statement:
--   Let $\varepsilon=1/512$ and $C_0=12$. For every integer $\Delta\ge16$ and every $m\ge0$,
--
--   $$W_m\le C_0\,\Delta^{\varepsilon(3-m)},$$
--
--   where $W_m$ is the sum of the weights $\alpha^{\#\text{ones}}\prod u_k$ over all binary patterns of length $m$ in which consecutive ones are separated by at least three zeros.
--
--   The geometric decay in $m$, with base $\Delta^{-\varepsilon}$, is what gives $O(\log_\Delta n)$ moves in the repair of §5.
--
--   Differences from the source: none.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 5.4, p.59 (PDF 61)

import Mathlib
import Definitions.Def_DynBrooks_Patterns

namespace DynBrooks

/-- **Lemma 5.4** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.59 (PDF 61)). Let `ε = 1/512` and `C₀ = 12`. For every `∆ ≥ 16` and `m ≥ 0`,
`W_m ≤ C₀ ∆^{ε(3−m)}`.

**Formalization Note.** `W Δ m` is the pattern sum of `DynBrooks.Patterns`; the exponent
`ε(3 − m)` is a real number (`Real.rpow`), negative for `m > 3`. -/
theorem lemma_5_4 (Δ : ℕ) (hΔ : 16 ≤ Δ) (m : ℕ) :
    W Δ m ≤ 12 * (Δ : ℝ) ^ ((1 / 512 : ℝ) * (3 - (m : ℝ))) := by sorry

end DynBrooks
