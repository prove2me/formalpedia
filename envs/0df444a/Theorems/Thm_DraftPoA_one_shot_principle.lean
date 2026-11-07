-- Prove2me | Theorems.Thm_DraftPoA_one_shot_principle
-- name    : DraftPoA.one_shot_principle
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:14.20203+00:00
-- url     : https://prove2.me/theorems/60de14d3-fad2-4fe1-a074-8e23a64fd6aa
-- title:
--   Standard facts: one-shot deviation principle for $\delta>0$; a pure SPE is an equilibrium of every kind
-- statement:
--   For every pure profile $b$ of the draft auction:
--
--   1. if $\delta>0$, $b$ is a pure subgame-perfect equilibrium if and only if no bidder has a profitable one-shot deviation (a change of her action at a single node) at any legal node at which an item remains;
--   2. a pure SPE is a pure Nash equilibrium;
--   3. a pure Nash equilibrium is a mixed Nash equilibrium and a correlated equilibrium (on one-point randomization devices) and a Bayes–Nash equilibrium for point-mass priors (one-point type spaces).
--
--   Point 1 reduces Claim B.6 to the one-shot Claims B.1–B.5; points 2–3 carry the lower bound to every equilibrium concept.
--
--   **Formalization Note** Strategies live on public nodes, so App. E's point (ii) (a strategy that also uses one's own losing bids does no better) is built into the model. SPE existence is not stated.
--
--   Differences from the source:
--   - encoding: mixed Nash, correlated and Bayes–Nash equilibria of a pure profile / point-mass priors → one-point devices and type spaces with Dirac measures; reason: a pure profile is the point-mass mixture
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §2, p.5 (PDF 6); App. E "Public strategies and the one-shot deviation principle", pp.32–33 (PDF 33–34)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria

open MeasureTheory

namespace DraftPoA

/-- The standard facts of §2, p.5 (PDF 6), justified in App. E, pp.32–33 (PDF 33–34)
(Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For a pure profile `b` on any grid: (i) when `δ > 0`, `b` is a pure SPE if and only if no bidder
has a profitable one-shot deviation at any legal node at which an item remains; (ii) a pure SPE
is a pure Nash equilibrium; (iii) a pure Nash equilibrium is a mixed Nash equilibrium and a
correlated equilibrium (one-point devices with the point mass), and a Bayes–Nash equilibrium for
point-mass priors (one-point type spaces).

**Formalization Note.** Strategies live on public nodes, so point (ii) of App. E is built into the
model; SPE existence is not stated (it is not used). -/
theorem one_shot_principle {n m : ℕ} [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) :
    (0 < δ → (IsPureSPE prio v b ↔ ∀ ν : Node n m, IsNode δ Mbar ν → (remaining ν).Nonempty →
      ∀ i, NoProfitableOneShot prio v b i ν)) ∧
    (IsPureSPE prio v b → IsPureNash prio v b) ∧
    (IsPureNash prio v b →
      IsMixedNash prio v (Ω := fun _ => Unit) (fun _ => Measure.dirac ()) (fun i _ => b i) ∧
      IsCorrelatedEq prio v (Measure.dirac ()) (fun _ : Unit => b) ∧
      IsBayesNash prio (T := fun _ => Unit) (Ω := fun _ => Unit) (fun _ => Measure.dirac ())
        (fun _ => Measure.dirac ()) (fun i _ => v i) (fun i _ _ => b i)) := by sorry

end DraftPoA
