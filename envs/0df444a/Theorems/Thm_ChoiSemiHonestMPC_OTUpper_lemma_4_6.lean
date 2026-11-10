-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_4_6
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:31:27.986222+00:00
-- url     : https://prove2.me/theorems/7fe8e615-ecc8-4ab5-b4a4-9a89e9bc181a
-- title:
--   Lemma 4.6 — wROT guarantee from an intermediate experiment
-- statement:
--   Let a discrete probability space carry both clients' outputs (`none` = failure) and the adversary's complete view. Let $G$ be an event of positive probability on which both outputs are present. Suppose that, conditional on $G$: (i) the outputs are $K$ independent ROT pairs; (ii) an intermediate view $(D,\mathrm{View}_1,\dots,\mathrm{View}_K)$ satisfies Lemma 4.2's hypotheses (`SeqFlagHyp`), with Info equal to $P$'s output, the hidden bits $P$'s hidden bits, and revelation probability $p$; (iii) the outputs and complete view are obtained from $P$'s output and the intermediate view by a fixed randomized map. Then the complete view can be simulated from $P$'s ideal view of $K$ independent $(p,p)$-wROT pairs, jointly with both outputs, with statistical error at most $\Pr[G^c]$. The failure probability is also at most $\Pr[G^c]$.
--
--   Differences from the source:
--   - reading: a protocol that generates K wROT pairs or fails, and an intermediate experiment with a designated view → a discrete probability space carrying both outputs (none = failure), the complete view, and the intermediate view; reason: the lemma is about these random variables only; the protocol enters through them
--   - generalization: (iii) the intermediate experiment satisfies the hypotheses of Lemma 4.5 jointly with both clients' outputs → (iii) (outputs, view) given G is obtained from (P's output, D, intermediate views) by a fixed randomized map F; reason: Lemma 4.5's hypotheses imply exactly this, so assuming it is weaker and the statement specializes to the source
--   - encoding: (ii) the hypotheses of Lemma 4.2; remaining view data generated from the reconstructed data → SeqFlagHyp on the conditional law given G, with Info = P’s output and B = P’s hidden bits; the remaining data are produced by F; reason: Lemma 4.2’s hypotheses on a discrete space
--   - encoding: for every passive adversary → one adversary’s view per application; reason: the lemma is applied adversary by adversary
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 4.6, p. 19 (PDF 21)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_AdaptiveQueries

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 4.6 (wROT guarantee from an intermediate experiment). -/
theorem lemma_4_6 {Ω V Dsp Vw : Type} (μ : PMF Ω) (K : ℕ) (P : Client) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (outA outB : Ω → Option (Bits K × Bits K)) (view : Ω → V)
    (G : Ω → Prop) (hG : 0 < probE μ G)
    (hsucc : ∀ ω ∈ μ.support, G ω → (outA ω).isSome ∧ (outB ω).isSome)
    (h_i : (pcond μ G).map (fun ω => (outA ω, outB ω)) =
      (rotOut K).map fun ab => (some ab.1, some ab.2))
    (D : Ω → Dsp) (iv : Ω → Fin K → Vw)
    (h_ii : SeqFlagHyp (pcond μ G) K
      (fun ω => ownOut P ((outA ω).getD default) ((outB ω).getD default))
      (fun ω => hiddenBits P ((outA ω).getD default) ((outB ω).getD default)) D iv p)
    (F : (Bits K × Bits K) → Dsp → (Fin K → Vw) → PMF V)
    (h_iii : (pcond μ G).map (fun ω => (outA ω, outB ω, view ω)) =
      (pcond μ G).bind fun ω =>
        (F (ownOut P ((outA ω).getD default) ((outB ω).getD default)) (D ω) (iv ω)).map
          fun v => (outA ω, outB ω, v)) :
    ∃ sim : (Bits K × Bits K) × (Fin K → Option Bool) → PMF V,
      tvPMF (μ.map fun ω => (outA ω, outB ω, view ω))
          ((wrotIdeal K p p P).bind fun x =>
            (sim (ownOut P x.1 x.2.1, x.2.2)).map fun v => (some x.1, some x.2.1, v)) ≤
        1 - probE μ G ∧
      probE μ (fun ω => outA ω = none ∨ outB ω = none) ≤ 1 - probE μ G := by sorry

end ChoiSemiHonestMPC.OTUpper
