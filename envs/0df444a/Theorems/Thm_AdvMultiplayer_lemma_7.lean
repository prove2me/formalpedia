-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_7
-- name    : AdvMultiplayer.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:16:08.718139+00:00
-- url     : https://prove2.me/theorems/9bd644e7-a9b3-4e8f-8ead-c7ceda1ea33c
-- title:
--   Lemma 7 — message decoding
-- statement:
--   Throughout, the rewards are rounded, the identification array is arbitrary and fixed first, and probabilities are over the fresh-row law: independent complete rows, private tapes, and $J$ read from the coordinator's tape. On the construction branch, work through the first queue-overflow update or the horizon. With probability at least $1-N^{-2}$, no completed batch has a unique solution different from the word currently encoded on its channel that passes (35), and no completed batch formed entirely from one fixed awaited word has multiple solutions. On this event, an awaited word is accepted within $2Q_{\mathrm{dec}}$ positive receiver observations after its sender fixes that word, within this prefix and provided service continues.
--
--   Differences from the source:
--   - reading: an awaited word is accepted within 2Q_dec positive receiver observations, provided service continues → if the word stays awaited on rounds t₀,…,t₁ and those rounds hold at least 2Q_dec positives, it is accepted in them; reason: this is the sentence with its proviso as a hypothesis
--   - encoding: the deterministic part holds on the event → stated almost surely; reason: the executions are defined on tapes of any real values
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 7, p.21

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 7 (message decoding).** Gan, arXiv:2610.05688, Lemma 7, p.21. In the fresh-row reference
execution on the construction branch, through the first queue-overflow update or the horizon: with
probability at least `1 - N⁻²` there is no decoder failure; on this event an awaited word is accepted
within `2Q_dec` positive receiver observations after its sender fixes that word, within this prefix and
provided service continues.

**Formalization Note.** "Provided service continues" is the hypothesis that the word stays awaited on
`t₀, …, t₁`, the rounds after the sender fixes it. Followers are `1 ≤ k ≤ d`. The identification array
and the rounded matrix are arbitrary and fixed first. -/
theorem lemma_7 (p : Size) (hb : p.branch) (idA : IdArray p) (r : Rewards p) (hr : IsRounded p r) :
    freshLaw p {x | ∃ t ∈ Finset.Icc 1 p.T, (t : ℕ∞) ≤ tauPhys p (idA, x.1) (freshTrace p idA r x) ∧
        decoderFailure p (freshTrace p idA r x) t} ≤ ENNReal.ofReal (1 / (p.N : ℝ) ^ 2) ∧
    ∀ᵐ x ∂(freshLaw p),
      (∀ t ∈ Finset.Icc 1 p.T, (t : ℕ∞) ≤ tauPhys p (idA, x.1) (freshTrace p idA r x) →
        ¬ decoderFailure p (freshTrace p idA r x) t) →
      ∀ (dir : Bool), ∀ k ∈ Finset.Icc 1 p.d, ∀ (w : Word p) (t₀ t₁ : ℕ), 1 ≤ t₀ → t₁ ≤ p.T →
        (t₁ : ℕ∞) ≤ tauPhys p (idA, x.1) (freshTrace p idA r x) →
        Awaited p (freshTrace p idA r x) dir k w t₀ t₁ →
        2 * p.Qdec ≤ positiveCount p (idA, x.1) (freshTrace p idA r x) dir k t₀ t₁ →
        ∃ t ∈ Finset.Icc t₀ t₁, acceptedOn p (freshTrace p idA r x) t dir k w := by sorry

end AdvMultiplayer
