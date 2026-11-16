-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_Supplement_theorem_4_1
-- name    : ConcurrentStochasticApprox.Approx.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:33:01.557069+00:00
-- url     : https://prove2.me/theorems/0f45fa77-0842-4011-b87e-e8d64d98d325
-- title:
--   Theorem 4.1 (companion theorem; not used in the proof of the goal) — Exact decision hardness and real-theory upper bounds
-- statement:
--   For concurrent stochastic games with rational transition probabilities, consider exact decision at a specified state and an arbitrary rational threshold: whether the reachability value, or the limit-average value with rational $[0,1]$-valued rewards, is at least that threshold. For each of these two objectives, both assertions hold:
--
--   1. There exists a polynomial-time many-one reduction from PosSLP to its CsgDecision language. For every binary input string, including malformed circuits and circuits with nonpositive output, the reduction outputs an encoding of a valid game with exactly two actions per player, deterministic transitions, two distinct absorbing states, and sure reachability of these states from every start under every action sequence. The output threshold is exactly $1/2$. There is no extra condition on the target set or reward function.
--   2. The CsgDecision language has polynomial-time many-one reductions to both the existential and the universal theory of the reals:
--   $$\mathrm{CsgDecision}_{\mathrm{Reach}},\ \mathrm{CsgDecision}_{\mathrm{LimAvg}}\ \in\ \exists\mathbb R\cap\mathrm{co}\text{-}\exists\mathbb R.$$
--
--   PosSLP asks whether a division-free, variable-free integer circuit with literals $0,1$ and operations $+,-,\times$ has positive output. ETR and UTR quantify over real assignments to Boolean combinations of polynomial comparisons with binary integer constants. Invalid game encodings are no-instances. The reductions use one uniform polynomial-time machine for all input lengths. This is a companion exact-decision theorem, independent of the approximation goal.
--
--   Differences from the source:
--   - encoding: CsgDecision, PosSLP, ETR and UTR with polynomial-time many-one reductions → binary languages using published game and circuit codes, expression-tree real sentences and CookPvsNP polynomial time; reason: fixes explicit self-delimiting representations and rejects malformed strings while retaining every input and every image restriction
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), Theorem 4.1, printed 10 (PDF 12)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_RealTheory
import Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_Decision
import Definitions.Def_PosSLPBounds_Deterministic_BinaryCircuits

namespace ConcurrentStochasticApprox.Approx.Supplement

/-- Theorem 4.1, both objectives and both bounds. The reductions output restricted
instances for every binary string, including malformed and nonpositive PosSLP inputs. -/
theorem theorem_4_1 :
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ x, (PosSLPBounds.Deterministic.posSLP x ↔ f x ∈ reachDecision) ∧
        f x ∈ restrictedReachCodes) ∧
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ x, (PosSLPBounds.Deterministic.posSLP x ↔ f x ∈ limAvgDecision) ∧
        f x ∈ restrictedLimAvgCodes) ∧
    (InExistsR reachDecision ∧ InCoExistsR reachDecision) ∧
    (InExistsR limAvgDecision ∧ InCoExistsR limAvgDecision) := by sorry

end ConcurrentStochasticApprox.Approx.Supplement
