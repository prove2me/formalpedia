-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_proposition_A_1
-- name    : CommThresholdPR.StrongConverse.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:32.401279+00:00
-- url     : https://prove2.me/theorems/03a5fc11-26ab-48e2-95f3-3f57c42d45ea
-- title:
--   Proposition A.1 — transcript factorization, outputs and prefix locality
-- statement:
--   Fix a finite binary protocol with independent private randomness and an arbitrary joint input law. For each positive-probability public seed $r$ and complete transcript $t$, there are nonnegative functions $u_{r,t}$ and $v_{r,t}$ with
--   $$\Pr[T=t\mid X=x,Y=y,R_{\rm pub}=r]=u_{r,t}(x)v_{r,t}(y)$$
--   whenever the conditioning event has positive probability. At every positive-probability complete conditioning value,
--   $$P(A,B\mid X,Y,R_{\rm pub},T)=P(A\mid X,R_{\rm pub},T)P(B\mid Y,R_{\rm pub},T).$$
--   At every public transcript prefix, the next message is conditionally independent of the other input given the sender's input and public history. These are three separate conclusions; the statement includes all of them. They supply the protocol locality interface.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: finite joint laws, base-two information and conditioning at positive-probability values → Mathlib PMF laws, finite entropy differences and explicit positive-probability conditional rows; reason: the representation changes no finite distribution; support mismatches retain infinite divergence and null conditional rows are used only as arbitrary normalized fallbacks
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Proposition A.1, p. 29, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem proposition_A_1 (μ : PMF (X × Y)) (π : Protocol X Y A B) :
    (∀ r : Fin π.publicSize, π.publicLaw r ≠ 0 → ∀ t : (π.tree r).Trace,
      ∃ (u : X → ℝ) (v : Y → ℝ), (∀ x, 0 ≤ u x) ∧ (∀ y, 0 ≤ v y) ∧
        ∀ x y, 0 < prob (π.law μ) (fun z => z.x = x ∧ z.y = y ∧ z.v.1 = r) →
          cprob (π.law μ) (fun z => z.v = ⟨r,t⟩)
            (fun z => z.x = x ∧ z.y = y ∧ z.v.1 = r) = u x * v y) ∧
    localOutputs (π.law μ) ∧
    (∀ (r : Fin π.publicSize) (h : List Bool) (sender : Bool),
      (π.tree r).senderAt h = some sender → ∀ x y,
      0 < prob (π.law μ) (fun z => z.x = x ∧ z.y = y ∧ π.prefixEvent r h z) →
      ∀ b : Bool, cprob (π.law μ) (π.nextEvent h b)
        (fun z => z.x = x ∧ z.y = y ∧ π.prefixEvent r h z) =
      if sender then cprob (π.law μ) (π.nextEvent h b)
        (fun z => z.x = x ∧ π.prefixEvent r h z)
      else cprob (π.law μ) (π.nextEvent h b)
        (fun z => z.y = y ∧ π.prefixEvent r h z)) := by sorry

end CommThresholdPR.StrongConverse
