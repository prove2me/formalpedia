-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_4
-- name    : BlottoFPTAS.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:56.36835+00:00
-- url     : https://prove2.me/theorems/f9c59176-3edd-4d9e-9ff0-de88c09e2f58
-- title:
--   Lemma 5.4 — a tuple of open/closed threshold choices is affordable iff (10); one deviation per affordable tuple attains U_w(P; c′)
-- statement:
--   Let $c'>0$ and finite threshold sets $T_j\subseteq[0,\infty)$ containing $0$. (i) Fix one choice on each battlefield $j$ at a threshold $t_j\in T_j$, some open and some closed. There is a deviation $y\in X(c')$ making all the specified choices if and only if
--   $$\sum_jt_j\le c',\quad\text{with strict inequality if at least one choice is open.}\tag{10}$$
--   (ii) Consequently, for battlefield values $w$ and a distribution $P$ on allocations whose bids on each battlefield $j$ lie in $T_j$: choosing one feasible deviation making each tuple of choices that satisfies (10), the largest expected payoff against $P$ among these finitely many deviations is $U_w(P;c')$; in particular the supremum is attained. This is what makes the opponent's best response a finite object in §5.2.
--
--   Differences from the source:
--   - generalization: battlefield values w (positive in the paper) → any real vector w; reason: the payoff of a deviation depends only on its choices whatever the signs of w; positive values are a special case
--   - encoding: a choice at t_j, open or closed; one chosen deviation per tuple; the largest payoff → a pair (t_j, flag); an arbitrary selection function dev on affordable tuples; IsGreatest of the set of their expected payoffs; reason: Lean convention; the statement holds for every selection, as the paper's 'choose one' requires
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 32, Lemma 5.4

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Thresholds

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 5.4** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 32).
Let `c' > 0` and finite threshold sets `T_j ⊆ [0, ∞)` containing `0`. (i) For thresholds
`t_j ∈ T_j` and open/closed flags `o_j`, some deviation `y ∈ X(c')` makes all the choices iff
`∑_j t_j ≤ c'`, strictly if some choice is open (10). (ii) For values `w` and a probability
distribution `P` whose bids on each battlefield `j` lie in `T_j`, and any choice of one feasible
deviation `dev t o` making each tuple of choices satisfying (10), the largest expected payoff
against `P` among these deviations is `U_w(P; c')`; in particular the supremum is attained. -/
theorem lemma_5_4 {m : ℕ} (T : Fin m → Finset ℝ) (hT0 : ∀ j, (0 : ℝ) ∈ T j)
    (hTnn : ∀ j, ∀ t ∈ T j, 0 ≤ t) (c' : ℝ) (hc' : 0 < c') :
    (∀ (t : Fin m → ℝ) (o : Fin m → Bool), (∀ j, t j ∈ T j) →
      ((∃ y ∈ X m c', ∀ j, Makes (T j) (t j) (o j) (y j)) ↔ Affordable t o c')) ∧
    (∀ (w : Fin m → ℝ) (P : Measure (Fin m → ℝ)), IsProbabilityMeasure P →
      P {x | ∀ j, x j ∈ T j}ᶜ = 0 →
      ∀ dev : (Fin m → ℝ) → (Fin m → Bool) → (Fin m → ℝ),
        (∀ t o, (∀ j, t j ∈ T j) → Affordable t o c' →
          dev t o ∈ X m c' ∧ ∀ j, Makes (T j) (t j) (o j) (dev t o j)) →
        IsGreatest
          {u : ℝ | ∃ (t : Fin m → ℝ) (o : Fin m → Bool), (∀ j, t j ∈ T j) ∧
            Affordable t o c' ∧ u = ∫ x, payoff w (dev t o) x ∂P}
          (U w P c')) := by sorry

end BlottoFPTAS.Main
