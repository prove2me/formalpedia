-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_4_1
-- name    : AlmostLinSubsetSum.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:28:56.934237+00:00
-- url     : https://prove2.me/theorems/5c05ef90-102d-4d66-bfb0-c74006215746
-- title:
--   Lemma 4.1 — size of the lifting parameter: $\tau_*^\delta\le w^\delta\le h\le\tau$ and $h^d|Q|\le w$
-- statement:
--   **Lemma 4.1** (p. 17). Let $Q=\prod_j[-q_j,q_j]$ with integers $q_j\ge1$, $\tau\ge1$ an integer, $w:=|\tau\cdot Q|$ and $h:=\lfloor\tau/\log^3 w\rfloor$ (5). Under (H2), $\tau\ge\max\{\tau_*,w^{2\delta}\}$, with $\tau_*$ sufficiently large,
--   $$\tau_*^\delta\le w^\delta\le h\le\tau\quad(6),\qquad h^d|Q|\le w\quad(7).$$
--
--   Formally: for every $d\ge1$ and $\delta>0$ there is $\tau_0$ such that for every $\tau_*\ge\tau_0$, all integers $q_j\ge1$ and every integer $\tau\ge1$ with $\tau_*\le\tau$ and $w^{2\delta}\le\tau$, the four inequalities hold, with $\log=\log_2$ and $|\cdot|$ the number of integer points.
--
--   Differences from the source:
--   - reading: log (base not stated) → log₂; reason: the paper names no base; the lemma's proof works for any fixed base
--   - generalization: δ = ε/8 for the fixed rational ε ∈ (0, 1/(2d)] of (3) → any real δ > 0; reason: the proof uses only δ > 0; the paper's δ is one such value
--   - reading: 'τ_* sufficiently large' (a global constant, (3)) → ∃ τ₀ (depending on d, δ) such that the conclusion holds for every τ_* ≥ τ₀; reason: explicit form of 'sufficiently large'
--   - generalization: the prepared instance satisfying (H1), (H2), (H3) in §4.1 → only the box, scale and (H2) are required; no item family or (H1), (H3); reason: the size inequalities involve no items, and the proof uses only (H2), positive dimension and integer half-widths
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 4.1 and (5), p. 17

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 4.1** (Size of the lifting parameter; Chen, Mao, Zhang 2026, p. 17). With
`w = |τ · Q|` and the lifting parameter `h := ⌊τ / log³ w⌋` (5), under (H2)
`τ ≥ max{τ_*, w^{2δ}}`:
`τ_*^δ ≤ w^δ ≤ h ≤ τ` (6) and `h^d |Q| ≤ w` (7).

Here `log` is `log₂`, `Q = ∏_j [−q_j, q_j]` with integers `q_j ≥ 1`, `τ ≥ 1` is an integer,
and "`τ_*` sufficiently large" is: there is `τ₀` (depending on `d`, `δ`) such that the
conclusion holds for every `τ_* ≥ τ₀`. -/
theorem lemma_4_1 :
    ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ →
    ∃ τ₀ : ℝ, ∀ τstar : ℝ, τ₀ ≤ τstar →
    ∀ (q : Fin d → ℕ), (∀ j, 1 ≤ q j) →
    ∀ τ : ℕ, 1 ≤ τ →
      τstar ≤ (τ : ℝ) →
      ((latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℕ) : ℝ) ^ (2 * δ) ≤ (τ : ℝ) →
      τstar ^ δ ≤ ((latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℕ) : ℝ) ^ δ ∧
      ((latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℕ) : ℝ) ^ δ ≤
        (⌊(τ : ℝ) / (Real.logb 2
          (latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℝ)) ^ 3⌋₊ : ℝ) ∧
      ⌊(τ : ℝ) / (Real.logb 2
          (latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℝ)) ^ 3⌋₊ ≤ τ ∧
      (⌊(τ : ℝ) / (Real.logb 2
          (latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) : ℝ)) ^ 3⌋₊) ^ d *
          latticeCount (box (fun j => (q j : ℝ))) ≤
        latticeCount (dilate (τ : ℝ) (box (fun j => (q j : ℝ)))) := by sorry

end AlmostLinSubsetSum.Main
