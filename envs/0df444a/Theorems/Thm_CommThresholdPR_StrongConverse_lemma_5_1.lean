-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_5_1
-- name    : CommThresholdPR.StrongConverse.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:58.725134+00:00
-- url     : https://prove2.me/theorems/4ab062d8-a370-4222-8351-4e994150f385
-- title:
--   Lemma 5.1 — error and information of the actual simulation
-- statement:
--   Let $q$ be the law of Construction 4.1 and $\pi$ the actual binary protocol of Construction 5.1. Write
--   $$\delta(n,p)=\sqrt{\frac{\ln2}{2n}\log_2\frac1p}.$$
--   When $\delta(n,p)\le1/2$, both bounds hold:
--   $$\operatorname{err}_{\mu}(\pi)\le\operatorname{err}(q)+\delta(n,p),$$
--   $$\operatorname{IC}_{\mu}(\pi)\le I_q(X;V\mid Y)+I_q(Y;V\mid X)+2L_{\rm in}\delta(n,p)+4h(\delta(n,p)).$$
--   The input law of $\pi$ is the original arbitrary joint law $\mu$. The divergence bound used in the proof is not assumed. These conclusions transfer the constructed law's error and information to an operational protocol.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
--   - encoding: Construction 5.1 with alternating messages and publicly fixed empty turns → the public augmented binary tree with actual binary encodings of finite auxiliary messages; reason: omitting publicly determined empty turns preserves the public history information; all nonempty messages are transmitted and only (J,X_<J) is public randomness
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 5.1, p. 17, (33)–(35), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_5_1 {n : ℕ} (hn : 0 < n) (e : Extraction X Y A B n)
    (R p ε : ℝ) (hsetup : e.Setup R p ε) (hδ : delta n p ≤ 1 / 2) :
    protocolError e.g e.μ (e.simulation hn) ≤ lawError e.g (e.q hn) + delta n p ∧
    (e.simulation hn).info e.μ ≤ infoSum (e.q hn) +
      2 * logInput X Y * delta n p + 4 * WildeQIT.binaryEntropy (delta n p) := by sorry

end CommThresholdPR.StrongConverse
