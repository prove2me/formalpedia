-- Prove2me | Theorems.Thm_BNCovPack_SetCover_lemma_5_1_ii
-- name    : BNCovPack.SetCover.lemma_5_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:06:05.451401+00:00
-- url     : https://prove2.me/theorems/6dffc879-6287-4925-91c2-82e1b884422a
-- title:
--   Lemma 5.1 (ii) — after augmenting a set, taking it or excluding it does not increase $\Phi$
-- statement:
--   Let $\Phi=\Phi_1+\Phi_2$ be the potential of Section 5.1 for a set-cover instance, with parameter $\alpha\ge 0$ and any natural number $OPT$. Let $(w,\mathcal C)$ be any state (weights and chosen family), $s$ a set, and $\delta\ge 0$. Write $w+\delta\mathbf 1_s$ for the weights with $w(s)$ increased by $\delta$. Then at least one of
--   $$\Phi\big(w+\delta\mathbf 1_s,\ \mathcal C\cup\{s\}\big)\le\Phi(w,\mathcal C)
--   \qquad\text{or}\qquad
--   \Phi\big(w+\delta\mathbf 1_s,\ \mathcal C\big)\le\Phi(w,\mathcal C)$$
--   holds.
--
--   This is the property that keeps the potential from increasing during the run of the online algorithm: whenever the weight of a set is augmented, one of the two decisions (take the set or leave it out) is available without increasing $\Phi$. It is the online form of the pessimistic-estimator step in derandomized rounding.
--
--   **Formalization Note** The page considers an augmentation $0\le\delta_s\le1$; the bound $\delta_s\le 1$ is not used by its argument and is dropped here, which makes the statement stronger. The statement is for every state $(w,\mathcal C)$, not only reachable ones.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 12, Lemma 5.1 (ii); proof pp. 13-14

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_BNCovPack_SetCover_Potential

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.1 (ii)** (Buchbinder–Naor 2009, p. 12; proof p. 13): when the weight of a set `s`
is augmented by `δ ≥ 0`, either taking `s` to the cover or excluding it does not increase `Φ`
(compared with its value before the augmentation). Stated for every state `(w, C)` and every
`α ≥ 0`; the paper's proof assumes `δ ≤ 1` but does not use it. -/
theorem lemma_5_1_ii {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ)
    (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hδ : 0 ≤ δ) :
    potential inst α OPT (Function.update w s (w s + δ)) (insert s C) ≤ potential inst α OPT w C ∨
    potential inst α OPT (Function.update w s (w s + δ)) C ≤ potential inst α OPT w C := by sorry

end BNCovPack.SetCover
