-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_6_1
-- name    : CommThresholdPR.StrongConverse.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:24.785205+00:00
-- url     : https://prove2.me/theorems/c9e7442e-efd4-4574-894b-b308900add9f
-- title:
--   Lemma 6.1 — a zero-message protocol from any local-output law
-- statement:
--   Let $\lambda$ be any finite joint law of $(X,Y,V,A,B)$ with
--   $$\lambda(a,b\mid x,y,v)=\lambda(a\mid x,v)\lambda(b\mid y,v)$$
--   whenever $\lambda(x,y,v)>0$. On inputs from $\lambda_{XY}$ there is an actual zero-message protocol $\sigma$ such that
--   $$\operatorname{err}_{\lambda_{XY}}(\sigma)\le\operatorname{err}(\lambda)+2\sqrt{(\ln2)[I_\lambda(X;V\mid Y)+I_\lambda(Y;V\mid X)]}.$$
--   The error of $\lambda$ is its failure probability for the total relation $g$. This statement applies to arbitrary local-output laws, independently of Construction 4.1, and concludes operational protocol existence.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: finite joint laws, base-two information and conditioning at positive-probability values → Mathlib PMF laws, finite entropy differences and explicit positive-probability conditional rows; reason: the representation changes no finite distribution; support mismatches retain infinite divergence and null conditional rows are used only as arbitrary normalized fallbacks
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma 6.1, p. 20, (42), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem lemma_6_1 {V : Type} [Fintype V] (g : TotalRelation X Y A B)
    (lam : PMF (Record X Y A B V)) (hlocal : localOutputs lam) :
    ∃ σ : Protocol X Y A B, σ.cost = 0 ∧
      protocolError g (lam.map (fun z => (z.x,z.y))) σ ≤
        lawError g lam + 2 * Real.sqrt (Real.log 2 * infoSum lam) := by sorry

end CommThresholdPR.StrongConverse
