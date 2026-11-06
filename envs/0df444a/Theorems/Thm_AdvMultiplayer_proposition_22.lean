-- Prove2me | Theorems.Thm_AdvMultiplayer_proposition_22
-- name    : AdvMultiplayer.proposition_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:16:07.671196+00:00
-- url     : https://prove2.me/theorems/fac5ee6c-547d-488c-a0a3-f2cb6f1d1cdb
-- title:
--   Proposition 22 — constructive initialization
-- statement:
--   Assuming (45), with probability at least $1-3/N$ over the identification array, for every fixed rounded matrix $r$ and every $j\in[M]$, with $\Delta_{\mathrm{boot}}=5N^{-2}$ and with probabilities over independent complete rows and private draws given $J=j$: (i) coupling Algorithms 7 and 8 on the same rows and private randomness, with probability at least $1-\Delta_{\mathrm{boot}}$ their actions, observations, gain weights, effective declarations, activation times, and ordinary registers agree through initialization; (ii) at the beginning of every reference launch round each follower is in the true-$j$ unoccupied state, the coordinator's scores and queues are zero, and for every $S$,
--   $$\mathbb E\sum_{t<\tau_L}r_t(S)\le CQ_{\mathrm{boot}}+CmT\Delta_{\mathrm{boot}}$$
--   for a universal $C$; (iii) the reference initialization and its corrections read only $R_j$, correcting a follower at launch or suppressing a prelaunch DOWN acceptance has probability at most $\Delta_{\mathrm{boot}}$, and the launch round is a stopping time for the selected-row and private history, given which the unexposed selected-row coordinates retain their product law.
--
--   Differences from the source:
--   - encoding: reads only R_j → two row families agreeing on row j give the same launch round, arms and corrections before launch; reason: this is what reading only R_j means
--   - reading: unexposed selected-row coordinates retain their product law → history events inside {τ_L = t} are independent of the coordinates of row j with calendar index t or later, whose unconditional law is the product law; reason: the paper uses “exposed” for variables generated in calendar order (the history F_t of p.14, the exposed history H_τ of p.18, Step 2 of Lemma 19), so the unexposed coordinates at the launch round are those with calendar index at least τ_L, and the history contains every earlier coordinate of row j
--   - encoding: the expectation in (ii) → `Integrable` is stated as a conclusion; reason: so that the integral is not a junk value
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Proposition 22, p.44, (53)

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Proposition 22 (constructive initialization).** Gan, arXiv:2610.05688, Proposition 22, p.44. With
probability at least `1 - 3/N` over the identification array, for every fixed rounded matrix `r` and every
`j ∈ [M]`, averaging over independent complete rows and private draws with `J = j`, (i)–(iii) hold, with
`Δ_boot = 5N⁻²` and a universal constant `C` quantified first.

**Formalization Note.** (i) couples Algorithms 7 and 8 on the same rows and tapes: `actualTrace` and
`refTrace`. "Ordinary learning and communication registers" are `fol` and `co`; "gain weights, effective
declarations, activation times" are `bootAgree`. In (iii) "reads only `R_j`" says that two row families
agreeing on row `j` give the same reference initialization, and "retain their product law" says that a
history event of `{τ_L = t}` is independent of the unexposed coordinates of row `j`, whose law under the
product measure is the product law. -/
theorem proposition_22 : ∃ C : ℝ, 0 < C ∧ ∀ (p : Size) (_ : p.branch),
    ∃ G : Set (IdArray p), MeasurableSet G ∧ ENNReal.ofReal (1 - 3 / (p.N : ℝ)) ≤ idLaw p G ∧
      ∀ idA ∈ G, ∀ r : Rewards p, IsRounded p r → ∀ j ∈ Finset.Icc 1 p.M,
        -- (i)
        ENNReal.ofReal (1 - p.Dboot) ≤ freshLaw p {x |
          (∀ t ∈ Finset.Icc 1 p.T, t < launchRound p (refTrace p idA r j x) →
            (actualTrace p idA r j x t).labels = (refTrace p idA r j x t).labels ∧
            (actualTrace p idA r j x t).obs = (refTrace p idA r j x t).obs) ∧
          (∀ t ∈ Finset.Icc 1 p.T, t ≤ launchRound p (refTrace p idA r j x) → ∀ i,
            bootAgree p ((actualTrace p idA r j x t).pre i) ((refTrace p idA r j x t).pre i) ∧
            ((actualTrace p idA r j x t).pre i).fol = ((refTrace p idA r j x t).pre i).fol ∧
            ((actualTrace p idA r j x t).pre i).co = ((refTrace p idA r j x t).pre i).co)} ∧
        -- (ii)
        (∀ x, launchRound p (refTrace p idA r j x) ≤ p.T →
          (∀ i, i ≠ coordinator p → trueUnoccupied p j
            ((refTrace p idA r j x (launchRound p (refTrace p idA r j x))).pre i)) ∧
          (∀ a, ((refTrace p idA r j x (launchRound p (refTrace p idA r j x))).pre
            (coordinator p)).co.z a = 0) ∧
          (∀ a, ((refTrace p idA r j x (launchRound p (refTrace p idA r j x))).pre
            (coordinator p)).co.Bq a = 0)) ∧
        (∀ S ∈ mSets p,
          Integrable (fun x => ∑ t ∈ Finset.Ico 1 (launchRound p (refTrace p idA r j x)),
            setReward p r t S) (freshLaw p) ∧
          ∫ x, (∑ t ∈ Finset.Ico 1 (launchRound p (refTrace p idA r j x)), setReward p r t S)
              ∂(freshLaw p)
            ≤ C * p.Qboot + C * p.m * p.T * p.Dboot) ∧
        -- (iii)
        (∀ x x' : FreshΩ p, x.2 = x'.2 →
          maskRows p (fun q _ _ => decide (q.val + 1 = j)) (fun q _ _ => decide (q.val + 1 = j))
              (fun q _ _ _ => decide (q.val + 1 = j)) x.1 =
            maskRows p (fun q _ _ => decide (q.val + 1 = j)) (fun q _ _ => decide (q.val + 1 = j))
              (fun q _ _ _ => decide (q.val + 1 = j)) x'.1 →
          launchRound p (refTrace p idA r j x) = launchRound p (refTrace p idA r j x') ∧
          ∀ t ∈ Finset.Icc 1 p.T, t < launchRound p (refTrace p idA r j x) →
            (refTrace p idA r j x t).labels = (refTrace p idA r j x' t).labels ∧
            (refTrace p idA r j x t).corrected = (refTrace p idA r j x' t).corrected) ∧
        freshLaw p {x | ∃ t ∈ Finset.Icc 1 p.T, t ≤ launchRound p (refTrace p idA r j x) ∧
            ∃ i, (refTrace p idA r j x t).corrected i = true ∨
              (t < launchRound p (refTrace p idA r j x) ∧
                ((refTrace p idA r j x t).logs i).filtered = true)}
          ≤ ENNReal.ofReal p.Dboot ∧
        IsStoppingTime (selHistory p j)
          (fun x => ((launchRound p (refTrace p idA r j x) : ℕ) : WithTop ℕ)) ∧
        ∀ (t : ℕ) (A : Set (FreshΩ p)), MeasurableSet[(selHistory p j) t] A →
          A ⊆ {x | launchRound p (refTrace p idA r j x) = t} →
          ∀ B : Set (Rows p), MeasurableSet B →
            freshLaw p (A ∩ futureSel p j t ⁻¹' B) =
              freshLaw p A * freshLaw p (futureSel p j t ⁻¹' B) := by sorry

end AdvMultiplayer
