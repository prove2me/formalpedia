-- Prove2me | Theorems.Thm_CalibeatBandit_rec_identity_C_1
-- name    : CalibeatBandit.rec_identity_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:02.217173+00:00
-- url     : https://prove2.me/theorems/71266158-1bed-4011-b0d9-0feb062b93a1
-- title:
--   §C.1 (p.30) — $\mathbb E[R^{\mathrm{Rec},p}_T]=\mathbb E[\mathrm{Rec}_T]$
-- statement:
--   Consider any learner and any run of the interaction protocol, with $p_t$ the learner's mixed strategy in round $t$. Then
--   $$\mathbb E\bigl[R^{\mathrm{Rec},p}_T\bigr]=\mathbb E[\mathrm{Rec}_T]-\sum_{t=1}^T\mathbb E\bigl[\langle p_t,y_t\rangle-y_t(I_t)\bigr],$$
--   and $\mathbb E[\langle p_t,y_t\rangle-y_t(I_t)]=0$ for every round $t$. Hence the expected pseudo reward loss is the expected reward loss.
--
--   This converts the bound on $\mathbb E[R^{\mathrm{Rec},p}_T]$ into the bound on $\mathbb E[\mathrm{Rec}_T]$ in Lemma 3.1 and Theorem 3.2.
--
--   **Formalization Note** $p_t$ is `run.played t`, the policy evaluated on the learner's observations.
--
--   Differences from the source:
--   - generalization: the learner of Algorithm 1 (and, by the proof of Theorem 3.2, the bandit algorithm) → every learner policy; reason: the argument uses only that $I_t$ has conditional law $p_t$ given the past and $y_t$; both algorithms are instances
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: in every run the integrands are bounded and almost everywhere measurable (the conditional law pins $p_t$ a.s.), so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.1, proof of Lemma C.1, p.30 (PDF 30); reused in the proof of Theorem 3.2, p.36

import Mathlib
import Definitions.Def_CalibeatBandit_ProtocolRun
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **The expected pseudo reward loss is the expected reward loss** (§C.1, proof of Lemma C.1,
p.30). In every run of the §2.1 protocol, with `p_t` the learner's mixed strategy,
`E[R^{Rec,p}_T] = E[Rec_T] − ∑_{t=1}^T E[⟨p_t, y_t⟩ − y_t(I_t)]`, and the expectation of
`⟨p_t, y_t⟩ − y_t(I_t)` is zero for every round.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.1, proof of Lemma C.1, p.30; reused in the proof of Theorem 3.2, p.36 ("the same
conversion … still holds here").

**Formalization Note.** Stated for an arbitrary learner `policy` (the paper uses it for
Algorithm 1 and for the bandit algorithm); `p_t` is `run.played t`. Rounds are `0, …, T − 1`;
`E` is the Bochner integral; `⟨p, y⟩` is `p ⬝ᵥ y`. -/
theorem rec_identity_C_1 {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (policy : Policy K) (run : ProtocolRun K T P policy) :
    ∫ ω, pseudoRewardLoss T (fun t => run.played t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P
      = ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        - ∑ t ∈ Finset.range T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P ∧
    ∀ t < T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P = 0 := by sorry

end CalibeatBandit
