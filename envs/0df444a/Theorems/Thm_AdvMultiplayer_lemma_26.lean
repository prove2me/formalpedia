-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_26
-- name    : AdvMultiplayer.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:01.239296+00:00
-- url     : https://prove2.me/theorems/e6e7f35d-2d91-4906-9dd6-7ea1591581ee
-- title:
--   Lemma 26 — uniform identification-array guarantees
-- statement:
--   On the construction branch, with probability at least $1-3/N$, the identification array satisfies: (i) for every time $t$ and bit $e$, at least $A/3$ indices have $I_u(t)=e$; (ii) every set of $6b_N$ distinct calendar times has fewer than $L_0$ indices whose ID bit is one at every one of those times; (iii) for every block $s$ and every binary string $x$ on it, at least $3A/4$ indices satisfy, simultaneously for every interval $D$ of the block and $e\in\{0,1\}$,
--   $$\sum_{t\in D}x_t\mathbf 1\{I_u(t)=e\}\ge\frac{S_D(x)}3-8b_N.$$
--
--   Differences from the source:
--   - reading: no hypothesis in the statement → construction branch (45); reason: the proof opens “On the construction branch”, and A and L₀ are defined only there (App. B.1)
--   - encoding: a string x on block s → the restriction of x : Fin T → Bool; reason: same strings; rounds outside the block are ignored
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 26, p.59, (68)

import Mathlib
import Definitions.Def_AdvMultiplayer_Table

open MeasureTheory

namespace AdvMultiplayer

open Classical in
/-- **Lemma 26 (uniform identification-array guarantees).** Gan, arXiv:2610.05688, Lemma 26, p.59, (68).
With probability at least `1 - 3/N`: (i) for every time and bit at least `A/3` indices have `I_u(t) = e`;
(ii) every set of `6b_N` distinct calendar times has fewer than `L₀` indices whose bit is one at all of
them; (iii) for every block `s` and string `x`, at least `3A/4` indices satisfy (68) simultaneously for
every interval of the block and every bit.

**Formalization Note.** On the construction branch, the section's standing assumption: `A` and `L₀` are
defined only there. Block `s` is the set of rounds `t` with `⌊(t-1)/B_boot⌋ = s - 1`; an interval of the
block is its intersection with `[a, b]`. A string on the block is the restriction of `x : Fin T → Bool`.
-/
theorem lemma_26 (p : Size) (hb : p.branch) :
    ENNReal.ofReal (1 - 3 / (p.N : ℝ)) ≤ idLaw p {I : IdArray p |
      (∀ (t : Fin p.T) (e : Bool),
        (p.A : ℝ) / 3 ≤ ((Finset.univ.filter fun u => I u t = e).card : ℝ)) ∧
      (∀ S : Finset (Fin p.T), S.card = 6 * p.bN →
        (Finset.univ.filter fun u => ∀ t ∈ S, I u t = true).card < p.L0) ∧
      (∀ s ∈ Finset.Icc 1 p.nboot, ∀ x : Fin p.T → Bool,
        3 * (p.A : ℝ) / 4 ≤ ((Finset.univ.filter fun u => ∀ (a b : ℕ) (e : Bool),
          (((Finset.univ.filter fun t : Fin p.T =>
              t.val / p.Bboot + 1 = s ∧ a ≤ t.val + 1 ∧ t.val + 1 ≤ b ∧ x t = true).card : ℝ)) / 3
            - 8 * p.bN ≤
          ((Finset.univ.filter fun t : Fin p.T =>
              t.val / p.Bboot + 1 = s ∧ a ≤ t.val + 1 ∧ t.val + 1 ≤ b ∧ x t = true ∧
                I u t = e).card : ℝ)).card : ℝ))} := by sorry

end AdvMultiplayer
